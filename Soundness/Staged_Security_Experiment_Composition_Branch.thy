(*  Title:      Stark/Staged_Security_Experiment_Composition_Branch.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Branch
  imports Staged_Security_Experiment_Composition_Bounds
begin

text \<open>
  Branch-specific composition reductions.

  This layer introduces branch-tied events for the verifier result actually
  sampled by the checked experiment.  These events are suitable for
  verifier-local WP bounds and avoid broad existential side events.
\<close>

context soundness
begin

definition staged_proof_data_of_query_prefix
  :: "'f staged_query_prefix_data \<Rightarrow> 'f staged_proof_data"
  where
    "staged_proof_data_of_query_prefix prefix =
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
       staged_query_chunks = sqp_query_chunks prefix\<rparr>"

lemma checked_staged_transcript_program_query_prefix_map:
  "checked_staged_transcript_program A =
    checked_staged_query_challenge_prefix_program A rounds \<bind>
      (\<lambda>prefix. return (staged_proof_data_of_query_prefix prefix))"
  unfolding checked_staged_transcript_program_def
    checked_staged_query_challenge_prefix_program_def
    staged_alpha_prefix_program_def
    staged_proof_data_of_query_prefix_def Let_def
  by (simp add: sm_bind_assoc split_def split: prod.splits)

lemma staged_query_search_queries_rounds_eq_total:
  assumes wf: "staged_budget_wellformed budgets"
  shows
    "staged_query_search_queries budgets rounds =
      staged_attacker_query_budget budgets + staged_challenge_query_budget"
  using wf
  unfolding staged_query_search_queries_def
    staged_attacker_query_budget_def staged_challenge_query_budget_def
    staged_budget_wellformed_def
  by simp

lemma hash_relation_program_checked_staged_transcript_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (checked_staged_transcript_program A)"
proof -
  have prefix:
    "hash_relation_program R b
      (staged_query_search_queries budgets rounds)
      (checked_staged_query_challenge_prefix_program A rounds)"
    by (rule hash_relation_program_checked_staged_query_challenge_prefix_program
        [OF wf controlled _ fibers])
      simp
  have mapped:
    "hash_relation_program R b
      (staged_query_search_queries budgets rounds + 0)
      (checked_staged_query_challenge_prefix_program A rounds \<bind>
        (\<lambda>prefix. return (staged_proof_data_of_query_prefix prefix)))"
    by (rule hash_relation_program_bind)
      (rule prefix,
        simp add: hash_relation_program_zero[OF hash_map_preserving_return])
  have budget_eq:
    "staged_query_search_queries budgets rounds =
      staged_attacker_query_budget budgets + staged_challenge_query_budget"
    by (rule staged_query_search_queries_rounds_eq_total[OF wf])
  show ?thesis
    unfolding checked_staged_transcript_program_query_prefix_map
    using mapped budget_eq by simp
qed

definition checked_staged_transcript_initial_roots_relation
  :: "'f staged_adversary \<Rightarrow> 'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "checked_staged_transcript_initial_roots_relation A x y \<longleftrightarrow>
      (\<exists>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<and>
        y \<in> {staged_trace_root data,
          hd (staged_composition_fri_roots data)})"

lemma checked_staged_transcript_initial_roots_relation_fiber_bound_size:
  "card {y. checked_staged_transcript_initial_roots_relation A x y}
    \<le> size"
proof -
  have subset:
    "{y. checked_staged_transcript_initial_roots_relation A x y}
      \<subseteq> (UNIV :: 'f set)"
    by simp
  have finite_univ: "finite (UNIV :: 'f set)"
    by simp
  have "card {y. checked_staged_transcript_initial_roots_relation A x y}
      \<le> card (UNIV :: 'f set)"
    by (rule card_mono[OF finite_univ subset])
  also have "... = size"
    using size_card by simp
  finally show ?thesis .
qed

lemma checked_staged_transcript_initial_roots_relation_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_transcript_program A)
      (hash_relation_hit_event
        (checked_staged_transcript_initial_roots_relation A)
        adversary_initial_state)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have program:
    "hash_relation_program
      (checked_staged_transcript_initial_roots_relation A)
      size
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (checked_staged_transcript_program A)"
    by (rule hash_relation_program_checked_staged_transcript_program
        [OF wf controlled])
      (rule checked_staged_transcript_initial_roots_relation_fiber_bound_size)
  show ?thesis
    using program
    unfolding hash_relation_program_def hash_relation_budget_def
      staged_phase_relation_error_def
    by blast
qed

lemma checked_staged_transcript_with_alpha_prefix_initial_roots_relation_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (packed, attacker_state) \<Rightarrow>
          hash_relation_hit
            (checked_staged_transcript_initial_roots_relation A)
            adversary_initial_state attacker_state)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  let ?R = "checked_staged_transcript_initial_roots_relation A"
  let ?H =
    "\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (packed, attacker_state) \<Rightarrow>
        hash_relation_hit ?R adversary_initial_state attacker_state"
  have map_eq:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A) ?H
        adversary_initial_state =
      wp_event
        (checked_staged_transcript_with_alpha_prefix_program A \<bind>
          (\<lambda>packed. return (snd packed)))
        (hash_relation_hit_event ?R adversary_initial_state)
        adversary_initial_state"
    by (subst wp_event_bind_return_map)
      (simp add: hash_relation_hit_event_def split: option.splits prod.splits)
  also have "... =
      wp_event (checked_staged_transcript_program A)
        (hash_relation_hit_event ?R adversary_initial_state)
        adversary_initial_state"
    unfolding checked_staged_transcript_with_alpha_prefix_program_projection
    by simp
  also have "... \<le>
      staged_phase_relation_error size
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule checked_staged_transcript_initial_roots_relation_hit_bound
        [OF wf controlled])
  finally show ?thesis .
qed

definition staged_proof_transcript_length_bound :: nat
  where
    "staged_proof_transcript_length_bound =
      4 + ceil_log clength + length spec + ceil_log (maxDegree + 1) +
      rounds *
        (query_decommitment_transcript_length 0 +
          fri_layers_transcript_length (ceil_log clength)
            (clength * scale) +
          fri_layers_transcript_length (ceil_log (maxDegree + 1))
            (clength * scale))"

definition staged_concrete_transcript_target_error_bound :: prob
  where
    "staged_concrete_transcript_target_error_bound =
      nnreal
        (staged_proof_transcript_length_bound * verifier_hash_query_budget) /
      nnreal size"

lemma fri_layers_transcript_length_mono_layers:
  assumes "m \<le> n"
  shows "fri_layers_transcript_length m len \<le>
    fri_layers_transcript_length n len"
  using assms
proof (induction m arbitrary: n len)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then obtain n' where n_eq: "n = Suc n'"
    by (cases n) auto
  have m_le: "m \<le> n'"
    using Suc.prems n_eq by simp
  have rec:
    "fri_layers_transcript_length m (len div 2) \<le>
      fri_layers_transcript_length n' (len div 2)"
    by (rule Suc.IH[OF m_le])
  show ?case
    unfolding n_eq by simp (rule rec)
qed

lemma length_concat_eq_sum_list_map_length:
  "length (List.concat xss) = sum_list (map length xss)"
  by (induction xss) simp_all

lemma sum_list_map_const:
  "(\<Sum>x\<leftarrow>xs. c) = length xs * c"
  by (induction xs) simp_all

lemma staged_query_chunks_total_length_le:
  assumes match: "staged_query_chunks_match_verifier_lengths data query_idxs"
    and trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    and composition_len:
      "length (staged_composition_fri_roots data) \<le>
        ceil_log (maxDegree + 1)"
  shows
    "length (List.concat (staged_query_chunks data)) \<le>
      rounds *
        (query_decommitment_transcript_length 0 +
          fri_layers_transcript_length (ceil_log clength)
            (clength * scale) +
          fri_layers_transcript_length (ceil_log (maxDegree + 1))
            (clength * scale))"
proof -
  let ?Q =
    "query_decommitment_transcript_length 0 +
      fri_layers_transcript_length (ceil_log clength) (clength * scale) +
      fri_layers_transcript_length (ceil_log (maxDegree + 1))
        (clength * scale)"
  have chunks_len: "length (staged_query_chunks data) = rounds"
    using match unfolding staged_query_chunks_match_verifier_lengths_def
    by simp
  have chunk_bound:
    "\<And>chunk. chunk \<in> set (staged_query_chunks data) \<Longrightarrow>
      length chunk \<le> ?Q"
  proof -
    fix chunk
    assume chunk_in: "chunk \<in> set (staged_query_chunks data)"
    then obtain i where i_bound: "i < rounds"
      and chunk_eq: "chunk = staged_query_chunks data ! i"
      using chunks_len
      by (metis in_set_conv_nth)
    have chunk_len:
      "length chunk =
        verifier_query_round_transcript_length (query_idxs ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)"
      using match i_bound chunk_eq
      unfolding staged_query_chunks_match_verifier_lengths_def by simp
    have comp_mono:
      "fri_layers_transcript_length
          (length (staged_composition_fri_roots data))
          (clength * scale)
        \<le>
        fri_layers_transcript_length (ceil_log (maxDegree + 1))
          (clength * scale)"
      by (rule fri_layers_transcript_length_mono_layers[OF composition_len])
    show "length chunk \<le> ?Q"
      unfolding chunk_len verifier_query_round_transcript_length_def
        trace_len query_decommitment_transcript_length_def powers_scaled_def
      using comp_mono by simp
  qed
  have sum_bound:
    "(\<Sum>chunk\<leftarrow>staged_query_chunks data. length chunk) \<le>
      (\<Sum>chunk\<leftarrow>staged_query_chunks data. ?Q)"
    by (rule sum_list_mono) (rule chunk_bound)
  have concat_len:
    "length (List.concat (staged_query_chunks data)) =
      (\<Sum>chunk\<leftarrow>staged_query_chunks data. length chunk)"
    by (rule length_concat_eq_sum_list_map_length)
  also have "... \<le> (\<Sum>chunk\<leftarrow>staged_query_chunks data. ?Q)"
    by (rule sum_bound)
  also have "... = length (staged_query_chunks data) * ?Q"
    by (rule sum_list_map_const)
  also have "... = rounds * ?Q"
    using chunks_len by simp
  finally show ?thesis .
qed

lemma checked_staged_transcript_program_staged_proof_transcript_length_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
  shows "length (staged_proof_transcript data) \<le>
    staged_proof_transcript_length_bound"
proof -
  have shape:
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_alphas data) = length spec \<and>
     length (staged_composition_fri_roots data) =
       ceil_log (to_nat (staged_degree data) + 1) \<and>
     ceil_log (to_nat (staged_degree data) + 1) \<le>
       ceil_log (maxDegree + 1)"
    using checked_staged_transcript_program_outcome_shape
      [OF wf controlled outcome]
    by blast
  from checked_staged_transcript_program_query_chunks_match_verifier_lengths
      [OF outcome]
  obtain query_idxs where match:
    "staged_query_chunks_match_verifier_lengths data query_idxs"
    by blast
  have query_len:
    "length (List.concat (staged_query_chunks data)) \<le>
      rounds *
        (query_decommitment_transcript_length 0 +
          fri_layers_transcript_length (ceil_log clength)
            (clength * scale) +
          fri_layers_transcript_length (ceil_log (maxDegree + 1))
            (clength * scale))"
    by (rule staged_query_chunks_total_length_le[OF match])
      (use shape in simp_all)
  have header_len:
    "length
      (verifier_header_messages
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data))
      \<le> 4 + ceil_log clength + length spec + ceil_log (maxDegree + 1)"
    using shape unfolding verifier_header_messages_def by simp
  show ?thesis
    unfolding staged_proof_transcript_def
      staged_proof_transcript_length_bound_def
    using header_len query_len by simp
qed

lemma concrete_transcript_target_error_bound_from_length:
  assumes "length tr \<le> n"
  shows "concrete_transcript_target_error tr \<le>
    nnreal (n * verifier_hash_query_budget) / nnreal size"
proof -
  have "card (set tr) \<le> length tr"
    by (rule card_length)
  then have card_le: "card (set tr) \<le> n"
    using assms by linarith
  have mult_le:
    "card (set tr) * verifier_hash_query_budget \<le>
      n * verifier_hash_query_budget"
    by (rule mult_right_mono[OF card_le]) simp
  show ?thesis
    unfolding concrete_transcript_target_error_def
    by (rule nnreal_nat_divide_right_mono[OF mult_le])
qed

lemma checked_staged_transcript_with_alpha_prefix_program_data_outcome:
  assumes outcome:
    "Some (packed, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_with_alpha_prefix_program A)
          adversary_initial_state)"
  shows
    "Some (snd packed, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  using outcome
  unfolding checked_staged_transcript_with_alpha_prefix_program_projection
    [symmetric]
  by (rule_tac x=packed and t=attacker_state in set_dist_bindI) simp_all

lemma checked_staged_transcript_with_alpha_prefix_program_concrete_transcript_target_error_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (packed, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_with_alpha_prefix_program A)
            adversary_initial_state)"
  shows
    "concrete_transcript_target_error (staged_proof_transcript (snd packed))
      \<le> staged_concrete_transcript_target_error_bound"
proof -
  have data_out:
    "Some (snd packed, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    by (rule checked_staged_transcript_with_alpha_prefix_program_data_outcome
        [OF outcome])
  have len:
    "length (staged_proof_transcript (snd packed)) \<le>
      staged_proof_transcript_length_bound"
    by (rule checked_staged_transcript_program_staged_proof_transcript_length_bound
        [OF wf controlled data_out])
  show ?thesis
    unfolding staged_concrete_transcript_target_error_bound_def
    by (rule concrete_transcript_target_error_bound_from_length[OF len])
qed

definition checked_staged_security_with_actual_alpha_prefix_verifier_event
  :: "('f protocol_channel \<Rightarrow>
        (unit list \<times> 'f protocol_channel) option \<Rightarrow> bool)
      \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_actual_alpha_prefix_verifier_event P out
      \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, final_state) \<Rightarrow>
          (let packed = fst (fst x);
               data = snd packed;
               attacker_state = snd (fst x);
               result = snd x;
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in P s (Some (result, final_state))))"

definition checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, final_state) \<Rightarrow>
          (let packed = fst (fst x);
               prefix_state = snd (fst packed);
               data = snd packed;
               attacker_state = snd (fst x);
               result = snd x;
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>trace_table composition_table as query_idxs dg
              composition_fri_roots final rest trace_tree composition_tree.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            verifier_header_transcript s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              as dg composition_fri_roots final rest \<and>
            created_tree trace_table trace_tree final_state \<and>
            created_tree composition_table composition_tree final_state \<and>
            hash_map_new_output_hit
              (set_tree trace_tree \<union> set_tree composition_tree)
              prefix_state final_state))"

definition checked_staged_security_with_actual_alpha_prefix_branch_tree_output_case
  where
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_output_case
      P out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, final_state) \<Rightarrow>
          (let packed = fst (fst x);
               prefix_state = snd (fst packed);
               data = snd packed;
               attacker_state = snd (fst x);
               result = snd x;
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>trace_table composition_table as query_idxs dg
              composition_fri_roots final rest trace_tree composition_tree.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            verifier_header_transcript s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              as dg composition_fri_roots final rest \<and>
            created_tree trace_table trace_tree final_state \<and>
            created_tree composition_table composition_tree final_state \<and>
            P trace_tree composition_tree prefix_state final_state))"

definition checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit =
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_case
        (\<lambda>trace_tree composition_tree prefix_state final_state.
          hash_map_new_output_hit
            {value trace_tree, value composition_tree}
            prefix_state final_state)"

definition
  checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit =
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_case
        (\<lambda>trace_tree composition_tree prefix_state final_state.
          (\<exists>l v r. trace_tree = \<langle>l, v, r\<rangle> \<and>
            hash_map_new_output_hit (set_tree l \<union> set_tree r)
              prefix_state final_state) \<or>
          (\<exists>l v r. composition_tree = \<langle>l, v, r\<rangle> \<and>
            hash_map_new_output_hit (set_tree l \<union> set_tree r)
              prefix_state final_state))"

definition
  checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit
      out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, final_state) \<Rightarrow>
          (let packed = fst (fst x);
               prefix_state = snd (fst packed);
               data = snd packed;
               attacker_state = snd (fst x);
               result = snd x;
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>trace_table composition_table as query_idxs dg
              composition_fri_roots final rest trace_tree composition_tree.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            verifier_header_transcript s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              as dg composition_fri_roots final rest \<and>
            created_tree trace_table trace_tree final_state \<and>
            created_tree composition_table composition_tree final_state \<and>
            ((\<exists>l v r. trace_tree = \<langle>l, v, r\<rangle> \<and>
              hash_map_new_output_hit (set_tree l \<union> set_tree r)
                prefix_state s) \<or>
             (\<exists>l v r. composition_tree = \<langle>l, v, r\<rangle> \<and>
              hash_map_new_output_hit (set_tree l \<union> set_tree r)
                prefix_state s))))"

definition
  checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
      out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, final_state) \<Rightarrow>
          (let packed = fst (fst x);
               data = snd packed;
               attacker_state = snd (fst x);
               result = snd x;
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>trace_table composition_table as query_idxs dg
              composition_fri_roots final rest trace_tree composition_tree.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            verifier_header_transcript s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              as dg composition_fri_roots final rest \<and>
            created_tree trace_table trace_tree final_state \<and>
            created_tree composition_table composition_tree final_state \<and>
            ((\<exists>l v r. trace_tree = \<langle>l, v, r\<rangle> \<and>
              hash_map_new_output_hit (set_tree l \<union> set_tree r)
                s final_state) \<or>
             (\<exists>l v r. composition_tree = \<langle>l, v, r\<rangle> \<and>
              hash_map_new_output_hit (set_tree l \<union> set_tree r)
                s final_state))))"

definition
  checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit
      out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, final_state) \<Rightarrow>
          (let packed = fst (fst x);
               prefix_state = snd (fst packed);
               data = snd packed;
               attacker_state = snd (fst x);
               result = snd x;
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>trace_table composition_table as query_idxs dg
              composition_fri_roots final rest.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            verifier_header_transcript s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              as dg composition_fri_roots final rest \<and>
            hash_map_new_output_hit
              {staged_trace_root data, hd composition_fri_roots}
              prefix_state final_state))"

definition
  checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
  where
    "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
      out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, final_state) \<Rightarrow>
          (let packed = fst (fst x);
               prefix_state = snd (fst packed);
               data = snd packed;
               attacker_state = snd (fst x);
               result = snd x;
               s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>trace_table composition_table as query_idxs dg
              composition_fri_roots final rest.
            Some (result, final_state) \<in>
              set_dist (execute verify_monad s) \<and>
            accepted_with_bound_tables s (Some (result, final_state))
              trace_table composition_table as query_idxs \<and>
            verifier_header_transcript s
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              as dg composition_fri_roots final rest \<and>
            hash_map_new_output_hit
              {staged_trace_root data, hd composition_fri_roots}
              prefix_state s))"

lemma checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit_imp_initial_roots_relation_on_support:
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
      "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
        out"
  shows
    "case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), data), attacker_state),
          result), final_state) \<Rightarrow>
        hash_relation_hit
          (checked_staged_transcript_initial_roots_relation A)
          adversary_initial_state attacker_state"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state),
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
  from support_some obtain trans_out where trans_out:
      "Some (((prefix, prefix_state), data), attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_with_alpha_prefix_program A)
            adversary_initial_state)"
    unfolding
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have data_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    using checked_staged_transcript_with_alpha_prefix_program_data_outcome
      [OF trans_out]
    by simp
  from checked_staged_transcript_with_alpha_prefix_program_support
      [OF wf controlled trans_out]
  have prefix_out:
      "Some (prefix, prefix_state) \<in>
        set_dist
          (execute (staged_alpha_prefix_program A)
            adversary_initial_state)"
    by blast
  have initial_prefix: "adversary_initial_state \<le> prefix_state"
  proof -
    have program:
      "hash_target_program {} (staged_alpha_search_queries budgets 0)
        (staged_alpha_prefix_program A)"
      by (rule hash_target_program_staged_alpha_prefix_program
          [OF wf controlled])
    then show ?thesis
      using prefix_out
      unfolding hash_target_program_def hash_extension_preserving_def
      by blast
  qed
  from hit obtain trace_table composition_table as query_idxs dg
      composition_fri_roots final rest where
    verify_out:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        as dg composition_fri_roots final rest"
    and root_hit:
      "hash_map_new_output_hit
        {staged_trace_root data, hd composition_fri_roots}
        prefix_state ?s"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit_def
      Let_def
    by simp blast
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
        [OF wf controlled data_out])
  have header_eq:
    "as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     composition_fri_roots = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     rest = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  from root_hit obtain x y where
    y_in: "y \<in> {staged_trace_root data, hd composition_fri_roots}"
    and lookup_prefix_none: "fmlookup (HashMap prefix_state) x = None"
    and lookup_s: "fmlookup (HashMap ?s) x = Some y"
    unfolding hash_map_new_output_hit_def by blast
  have lookup_initial_none: "fmlookup (HashMap adversary_initial_state) x = None"
  proof (cases "fmlookup (HashMap adversary_initial_state) x")
    case None
    then show ?thesis .
  next
    case (Some old)
    have "fmlookup (HashMap prefix_state) x = Some old"
      by (rule hash_extension_lookup[OF Some initial_prefix])
    then show ?thesis
      using lookup_prefix_none by simp
  qed
  have lookup_attacker: "fmlookup (HashMap attacker_state) x = Some y"
    using lookup_s by simp
  have relation:
    "checked_staged_transcript_initial_roots_relation A x y"
  proof -
    have "y \<in>
        {staged_trace_root data, hd (staged_composition_fri_roots data)}"
      using y_in header_eq by auto
    then show ?thesis
      unfolding checked_staged_transcript_initial_roots_relation_def
      using data_out by blast
  qed
  have
    "hash_relation_hit
      (checked_staged_transcript_initial_roots_relation A)
      adversary_initial_state attacker_state"
    unfolding hash_relation_hit_def
    by (intro exI[of _ x] exI[of _ y] conjI)
      (use lookup_initial_none lookup_attacker relation in simp_all)
  then show ?thesis
    unfolding out_eq by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
  unfolding checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
proof (rule wp_event_bind_bound_by_head_event)
  show
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (\<lambda>out. case out of
        None \<Rightarrow> False
      | Some (packed, attacker_state) \<Rightarrow>
          hash_relation_hit
            (checked_staged_transcript_initial_roots_relation A)
            adversary_initial_state attacker_state)
      adversary_initial_state
      \<le> staged_phase_relation_error size
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_transcript_with_alpha_prefix_initial_roots_relation_hit_bound
        [OF wf controlled])
next
  show
    "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
      None \<Longrightarrow>
     (case None of None \<Rightarrow> False
      | Some (packed, attacker_state) \<Rightarrow>
          hash_relation_hit
            (checked_staged_transcript_initial_roots_relation A)
            adversary_initial_state attacker_state)"
    unfolding
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit_def
    by simp
next
  fix packed attacker_state out
  assume trans_out:
      "Some (packed, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_with_alpha_prefix_program A)
            adversary_initial_state)"
    and cont:
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
      "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
        out"
  have support:
    "out \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
            A)
          adversary_initial_state)"
    unfolding
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    by (rule_tac x=packed and t=attacker_state in set_dist_bindI)
      (use trans_out cont in simp_all)
  have rel:
    "case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), data), attacker_state),
          result), final_state) \<Rightarrow>
        hash_relation_hit
          (checked_staged_transcript_initial_roots_relation A)
          adversary_initial_state attacker_state"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit_imp_initial_roots_relation_on_support
        [OF wf controlled support hit])
  show
    "(case Some (packed, attacker_state) of
      None \<Rightarrow> False
    | Some (packed, attacker_state) \<Rightarrow>
        hash_relation_hit
          (checked_staged_transcript_initial_roots_relation A)
          adversary_initial_state attacker_state)"
    using cont rel
    by (cases out)
      (auto elim!: set_dist_bindE split: option.splits prod.splits)
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_imp_tree_output_hit:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_tree_output_hit out"
  using hit
  unfolding
    checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_def
    checked_staged_security_with_actual_alpha_prefix_tree_output_hit_def
    Let_def
  by (cases out) (fastforce split: prod.splits)+

lemma checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_imp_root_or_subtree:
  assumes hit:
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit
        out \<or>
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit
        out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_def
    by simp
next
  case (Some result_pack)
  then obtain x final_state where out_eq:
      "out = Some (x, final_state)"
    by (cases result_pack) simp
  from hit obtain trace_table composition_table as query_idxs dg
      composition_fri_roots final rest trace_tree composition_tree where
    body:
      "Some (snd x, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary (snd (fst x))
              (staged_proof_transcript (snd (fst (fst x))))))"
      "accepted_with_bound_tables
        (verifier_state_from_adversary (snd (fst x))
          (staged_proof_transcript (snd (fst (fst x)))))
        (Some (snd x, final_state)) trace_table composition_table as
        query_idxs"
      "verifier_header_transcript
        (verifier_state_from_adversary (snd (fst x))
          (staged_proof_transcript (snd (fst (fst x)))))
        (staged_trace_root (snd (fst (fst x))))
        (staged_trace_fri_roots (snd (fst (fst x))))
        (staged_trace_final (snd (fst (fst x))))
        as dg composition_fri_roots final rest"
      "created_tree trace_table trace_tree final_state"
      "created_tree composition_table composition_tree final_state"
      "hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        (snd (fst (fst (fst x)))) final_state"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_def
      Let_def
    by (auto split: prod.splits)
  from hash_map_new_output_hit_two_trees_root_or_subtree[OF body(6)]
  show ?thesis
  proof
    assume root_hit:
      "hash_map_new_output_hit {value trace_tree, value composition_tree}
        (snd (fst (fst (fst x)))) final_state"
    have
      "checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit
        out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit_def
        checked_staged_security_with_actual_alpha_prefix_branch_tree_output_case_def
        Let_def
      using body(1-5) root_hit
      by (cases x) (fastforce split: prod.splits)+
    then show ?thesis by simp
  next
    assume subtree:
      "(\<exists>l v r. trace_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r)
          (snd (fst (fst (fst x)))) final_state) \<or>
       (\<exists>l v r. composition_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r)
          (snd (fst (fst (fst x)))) final_state)"
    have
      "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit
        out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit_def
        checked_staged_security_with_actual_alpha_prefix_branch_tree_output_case_def
        Let_def
      using body(1-5) subtree
      by (cases x) (fastforce split: prod.splits)+
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_bound_from_root_and_subtree:
  assumes root_bound:
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit
      s \<le> R"
    and subtree_bound:
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit
      s \<le> S"
  shows
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      s \<le> R + S"
proof -
  have "wp_event m
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      s \<le>
    wp_event m
      (\<lambda>out.
        checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit
          out \<or>
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit
          out) s"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_imp_root_or_subtree)
  also have "... \<le>
      wp_event m
        checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit
        s +
      wp_event m
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit
        s"
    by (rule wp_event_union_bound)
  also have "... \<le> R + S"
    by (intro add_mono root_bound subtree_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit_imp_preverifier_or_verifier_on_support:
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
      "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit
        out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit
        out \<or>
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
        out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit_def
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_case_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state result final_state where
    out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state),
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
  from support_some obtain trans_out where trans_out:
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
  have prefix_s: "prefix_state \<le> ?s"
    by (rule
        alpha_prefix_hash_extends_verifier_state_from_adversary_right
        [OF prefix_ext])
  from hit obtain trace_table composition_table as query_idxs dg
      composition_fri_roots final rest trace_tree composition_tree where
    verify_out:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        as dg composition_fri_roots final rest"
    and trace_created:
      "created_tree trace_table trace_tree final_state"
    and composition_created:
      "created_tree composition_table composition_tree final_state"
    and subtree:
      "(\<exists>l v r. trace_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r)
          prefix_state final_state) \<or>
       (\<exists>l v r. composition_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r)
          prefix_state final_state)"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit_def
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_case_def
      Let_def
    by simp blast
  have s_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verify_out])
  from subtree show ?thesis
  proof
    assume trace_subtree:
      "\<exists>l v r. trace_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r)
          prefix_state final_state"
    then obtain l v r where trace_tree_eq: "trace_tree = \<langle>l, v, r\<rangle>"
      and tree_hit:
        "hash_map_new_output_hit (set_tree l \<union> set_tree r)
          prefix_state final_state"
      by blast
    from hash_map_new_output_hit_trans_decomp
        [OF prefix_s s_final tree_hit]
    show ?thesis
    proof
      assume pre:
        "hash_map_new_output_hit (set_tree l \<union> set_tree r)
          prefix_state ?s"
      have
        "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit
          out"
        unfolding out_eq
          checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit_def
          Let_def
        using verify_out bound header trace_created composition_created
          trace_tree_eq pre
        by simp blast
      then show ?thesis by simp
    next
      assume verifier:
        "hash_map_new_output_hit (set_tree l \<union> set_tree r)
          ?s final_state"
      have
        "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
          out"
        unfolding out_eq
          checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit_def
          Let_def
        using verify_out bound header trace_created composition_created
          trace_tree_eq verifier
        by simp blast
      then show ?thesis by simp
    qed
  next
    assume composition_subtree:
      "\<exists>l v r. composition_tree = \<langle>l, v, r\<rangle> \<and>
        hash_map_new_output_hit (set_tree l \<union> set_tree r)
          prefix_state final_state"
    then obtain l v r where
      composition_tree_eq: "composition_tree = \<langle>l, v, r\<rangle>"
      and tree_hit:
        "hash_map_new_output_hit (set_tree l \<union> set_tree r)
          prefix_state final_state"
      by blast
    from hash_map_new_output_hit_trans_decomp
        [OF prefix_s s_final tree_hit]
    show ?thesis
    proof
      assume pre:
        "hash_map_new_output_hit (set_tree l \<union> set_tree r)
          prefix_state ?s"
      have
        "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit
          out"
        unfolding out_eq
          checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit_def
          Let_def
        using verify_out bound header trace_created composition_created
          composition_tree_eq pre
        by simp blast
      then show ?thesis by simp
    next
      assume verifier:
        "hash_map_new_output_hit (set_tree l \<union> set_tree r)
          ?s final_state"
      have
        "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
          out"
        unfolding out_eq
          checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit_def
          Let_def
        using verify_out bound header trace_created composition_created
          composition_tree_eq verifier
        by simp blast
      then show ?thesis by simp
    qed
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit_bound_from_preverifier_and_verifier:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit
        adversary_initial_state \<le> P"
    and verifier_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
        adversary_initial_state \<le> V"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit
      adversary_initial_state \<le> P + V"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Sub =
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit"
  let ?Pre =
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit"
  let ?Verifier =
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit"
  have "wp_event ?M ?Sub adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?Pre out \<or> ?Verifier out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit_imp_preverifier_or_verifier_on_support
        [OF wf controlled])
  also have "... \<le>
      wp_event ?M ?Pre adversary_initial_state +
      wp_event ?M ?Verifier adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> P + V"
    by (intro add_mono pre_bound verifier_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit_imp_transcript_root_output_hit:
  assumes root_hit:
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit
      out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit
      out"
proof (cases out)
  case None
  then show ?thesis
    using root_hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit_def
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_case_def
    by simp
next
  case (Some result_pack)
  then obtain x final_state where out_eq:
      "out = Some (x, final_state)"
    by (cases result_pack) simp
  let ?packed = "fst (fst x)"
  let ?prefix_state = "snd (fst ?packed)"
  let ?data = "snd ?packed"
  let ?attacker_state = "snd (fst x)"
  let ?result = "snd x"
  let ?s =
    "verifier_state_from_adversary ?attacker_state
      (staged_proof_transcript ?data)"
  from root_hit obtain trace_table composition_table as query_idxs dg
      composition_fri_roots final rest trace_tree composition_tree where
    verify_out:
      "Some (?result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s (Some (?result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root ?data)
        (staged_trace_fri_roots ?data)
        (staged_trace_final ?data)
        as dg composition_fri_roots final rest"
    and trace_created:
      "created_tree trace_table trace_tree final_state"
    and composition_created:
      "created_tree composition_table composition_tree final_state"
    and tree_root_hit:
      "hash_map_new_output_hit
        {value trace_tree, value composition_tree}
        ?prefix_state final_state"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit_def
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_case_def
      Let_def
    by simp blast
  from bound obtain fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    header':
      "verifier_header_transcript ?s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and trace_bind:
      "merkle_root_binds_table fr' trace_table final_state"
    and composition_bind:
      "merkle_root_binds_table (hd composition_fri_roots')
        composition_table final_state"
    unfolding accepted_with_bound_tables_def by auto
  have header_eq:
    "fr' = staged_trace_root ?data \<and>
     f_fri_roots' = staged_trace_fri_roots ?data \<and>
     f_final' = staged_trace_final ?data \<and>
     dg' = dg \<and>
     composition_fri_roots' = composition_fri_roots \<and>
     final' = final \<and>
     rest' = rest"
    using verifier_header_transcript_unique[OF header' header]
    by simp
  then have fr_eq: "fr' = staged_trace_root ?data"
    and comp_roots_eq:
      "composition_fri_roots' = composition_fri_roots"
    by simp_all
  from trace_bind obtain trace_root_tree where
    trace_root_created:
      "created_tree trace_table trace_root_tree final_state"
    and trace_root_eq: "fr' = value trace_root_tree"
    unfolding merkle_root_binds_table_def by blast
  have trace_value_eq:
    "value trace_tree = staged_trace_root ?data"
    using created_tree_same_table_value_eq
        [OF trace_created trace_root_created]
      trace_root_eq fr_eq
    by simp
  from composition_bind obtain composition_root_tree where
    composition_root_created:
      "created_tree composition_table composition_root_tree final_state"
    and composition_root_eq:
      "hd composition_fri_roots' = value composition_root_tree"
    unfolding merkle_root_binds_table_def by blast
  have composition_value_eq:
    "value composition_tree = hd composition_fri_roots"
    using created_tree_same_table_value_eq
        [OF composition_created composition_root_created]
      composition_root_eq comp_roots_eq
    by simp
  have transcript_root_hit:
    "hash_map_new_output_hit
      {staged_trace_root ?data, hd composition_fri_roots}
      ?prefix_state final_state"
    using tree_root_hit trace_value_eq composition_value_eq by simp
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit_def
      Let_def
    using verify_out bound header transcript_root_hit
    by simp blast
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit_bound_from_transcript_roots:
  assumes root_bound:
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit
      s \<le> R"
  shows
    "wp_event m
      checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit
      s \<le> R"
  by (rule order.trans[OF _ root_bound])
    (rule wp_event_mono,
      rule
        checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit_imp_transcript_root_output_hit)

lemma checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit_imp_preverifier_or_verifier_on_support:
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
      "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit
        out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
        out \<or>
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
        out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state result final_state where
    out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state),
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
  from support_some obtain trans_out where trans_out:
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
  have prefix_s: "prefix_state \<le> ?s"
    by (rule
        alpha_prefix_hash_extends_verifier_state_from_adversary_right
        [OF prefix_ext])
  from hit obtain trace_table composition_table as query_idxs dg
      composition_fri_roots final rest where
    verify_out:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        as dg composition_fri_roots final rest"
    and root_hit:
      "hash_map_new_output_hit
        {staged_trace_root data, hd composition_fri_roots}
        prefix_state final_state"
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit_def
      Let_def
    by simp blast
  have s_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verify_out])
  from hash_map_new_output_hit_trans_decomp
      [OF prefix_s s_final root_hit]
  show ?thesis
  proof
    assume pre:
      "hash_map_new_output_hit
        {staged_trace_root data, hd composition_fri_roots}
        prefix_state ?s"
    have
      "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
        out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit_def
        Let_def
      using verify_out bound header pre
      by simp blast
    then show ?thesis by simp
  next
    assume verifier:
      "hash_map_new_output_hit
        {staged_trace_root data, hd composition_fri_roots}
        ?s final_state"
    have
      "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
        out"
      unfolding out_eq
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit_def
        Let_def
      using verify_out bound header verifier
      by simp blast
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit_bound_from_preverifier_and_verifier:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
        adversary_initial_state \<le> P"
    and verifier_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
        adversary_initial_state \<le> V"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit
      adversary_initial_state \<le> P + V"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Root =
    "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit"
  let ?Pre =
    "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit"
  let ?Verifier =
    "checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit"
  have "wp_event ?M ?Root adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?Pre out \<or> ?Verifier out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit_imp_preverifier_or_verifier_on_support
        [OF wf controlled])
  also have "... \<le>
      wp_event ?M ?Pre adversary_initial_state +
      wp_event ?M ?Verifier adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> P + V"
    by (intro add_mono pre_bound verifier_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit_bound_from_preverifier_and_verifier:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
        adversary_initial_state \<le> P"
    and verifier_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
        adversary_initial_state \<le> V"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit
      adversary_initial_state \<le> P + V"
proof -
  have root_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit
      adversary_initial_state \<le> P + V"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_output_hit_bound_from_preverifier_and_verifier
        [OF wf controlled pre_bound verifier_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit_bound_from_transcript_roots
        [OF root_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit_bound_from_preverifier_and_concrete_transcript_targets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
        adversary_initial_state \<le> P"
    and target_bound:
      "\<And>packed attacker_state.
        Some (packed, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_with_alpha_prefix_program A)
              adversary_initial_state) \<Longrightarrow>
        concrete_transcript_target_error (staged_proof_transcript (snd packed))
          \<le> V"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit
      adversary_initial_state \<le> P + V"
proof -
  have verifier_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit
      adversary_initial_state \<le> V"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_verifier_output_hit_bound_from_concrete_transcript_targets
        [OF target_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit_bound_from_preverifier_and_verifier
        [OF wf controlled pre_bound verifier_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_bound_from_preverifier_concrete_transcript_targets_and_subtree:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
        adversary_initial_state \<le> P"
    and target_bound:
      "\<And>packed attacker_state.
        Some (packed, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_with_alpha_prefix_program A)
              adversary_initial_state) \<Longrightarrow>
        concrete_transcript_target_error (staged_proof_transcript (snd packed))
          \<le> V"
    and subtree_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit
        adversary_initial_state \<le> S"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      adversary_initial_state \<le> P + V + S"
proof -
  have root_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit
      adversary_initial_state \<le> P + V"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_branch_tree_root_output_hit_bound_from_preverifier_and_concrete_transcript_targets
        [OF wf controlled pre_bound target_bound])
  have
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      adversary_initial_state \<le> (P + V) + S"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_bound_from_root_and_subtree
        [OF root_bound subtree_bound])
  then show ?thesis
    by (simp add: add.assoc)
qed

lemma checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_bound_from_preverifier_concrete_transcript_targets_and_split_subtree:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and root_pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
        adversary_initial_state \<le> P"
    and target_bound:
      "\<And>packed attacker_state.
        Some (packed, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_with_alpha_prefix_program A)
              adversary_initial_state) \<Longrightarrow>
        concrete_transcript_target_error (staged_proof_transcript (snd packed))
          \<le> V"
    and subtree_pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit
        adversary_initial_state \<le> SP"
    and subtree_verifier_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
        adversary_initial_state \<le> SV"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      adversary_initial_state \<le> P + V + SP + SV"
proof -
  have subtree_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit
      adversary_initial_state \<le> SP + SV"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_output_hit_bound_from_preverifier_and_verifier
        [OF wf controlled subtree_pre_bound subtree_verifier_bound])
  have
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      adversary_initial_state \<le> P + V + (SP + SV)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_bound_from_preverifier_concrete_transcript_targets_and_subtree
        [OF wf controlled root_pre_bound target_bound subtree_bound])
  then show ?thesis
    by (simp add: add.assoc)
qed

lemma checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection:
  "wp_event (checked_staged_security_experiment_with_data_state A)
    (staged_security_with_data_state_verifier_event P)
    adversary_initial_state =
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event P)
    adversary_initial_state"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event P)
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
        \<bind> (\<lambda>x. return (?project x)))
      (staged_security_with_data_state_verifier_event P)
      adversary_initial_state"
    using
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
      [of A]
    by simp
  also have "... =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. case out of
        None \<Rightarrow> staged_security_with_data_state_verifier_event P None
      | Some (x, t) \<Rightarrow>
          staged_security_with_data_state_verifier_event P
            (Some (?project x, t)))
      adversary_initial_state"
    by (rule wp_event_bind_return_map)
  also have "... =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event P)
      adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
    apply (rule arg_cong[where
        f="\<lambda>Q. wp_event
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
          Q adversary_initial_state"])
    apply (rule ext)
    apply (simp add: Let_def split: option.splits prod.splits)
    done
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_imp_prefix_or_branch_tree_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and bad:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space out \<or>
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
        out"
proof (cases out)
  case None
  then show ?thesis
    using bad
    unfolding
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state result final_state where
    out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state),
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
  from support_some obtain trans_out where trans_out:
      "Some (((prefix, prefix_state), data), attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_with_alpha_prefix_program A)
            adversary_initial_state)"
    and verify_out:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    unfolding
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  from checked_staged_transcript_with_alpha_prefix_program_support
      [OF wf controlled trans_out]
  have prefix_out:
      "Some (prefix, prefix_state) \<in>
        set_dist
          (execute (staged_alpha_prefix_program A)
            adversary_initial_state)"
    and root_eq: "staged_trace_root data = fst prefix"
    and trace_roots_eq:
      "staged_trace_fri_roots data = fst (snd prefix)"
    and trace_bs_eq:
      "staged_trace_fri_challenges data = fst (snd (snd prefix))"
    and trace_final_eq:
      "staged_trace_final data = snd (snd (snd prefix))"
    and prefix_ext: "prefix_state \<le> attacker_state"
    by blast+
  have prefix_tuple:
    "prefix =
      (staged_trace_root data, staged_trace_fri_roots data,
       staged_trace_fri_challenges data, staged_trace_final data)"
    by (cases prefix; cases "snd prefix"; cases "snd (snd prefix)")
      (use root_eq trace_roots_eq trace_bs_eq trace_final_eq in auto)
  have random_bad:
    "composition_randomization_bad ?s (Some (result, final_state))"
    using bad unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      Let_def
    by simp
  have alpha_hit:
    "alpha_bad_set_hit ?s composition_trace_bad_alpha_space
      (Some (result, final_state))"
    by (rule composition_randomization_bad_imp_alpha_bad_set_hit
        [OF random_bad])
  from alpha_hit obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and as_bad: "as \<in> composition_trace_bad_alpha_space trace_table"
    unfolding alpha_bad_set_hit_def by blast
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
  proof -
    have projected:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_transcript_with_alpha_prefix_program A \<bind>
              (\<lambda>packed. return (snd packed)))
            adversary_initial_state)"
      by (rule set_dist_bindI[OF trans_out]) simp
    have checked_builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
      using projected
      unfolding checked_staged_transcript_with_alpha_prefix_program_projection
      by simp
    show ?thesis
      by (rule checked_staged_transcript_program_outcome_header_transcript
          [OF wf controlled checked_builder])
  qed
  from bound obtain fr f_fri_roots f_final dg composition_fri_roots final
      rest where
    header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    unfolding accepted_with_bound_tables_def by blast
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
  have staged_bad:
    "staged_alphas data \<in> composition_trace_bad_alpha_space trace_table"
    using as_bad header_eq by simp
  have alphas_space: "staged_alphas data \<in> alpha_space"
    using staged_bad composition_trace_bad_alpha_space_subset_alpha_space
    by blast
  have prefix_s: "prefix_state \<le> ?s"
    by (rule
        alpha_prefix_hash_extends_verifier_state_from_adversary_right
        [OF prefix_ext])
  have s_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verify_out])
  have prefix_final: "prefix_state \<le> final_state"
    by (rule hash_ext_trans[OF prefix_s s_final])
  show ?thesis
  proof (rule
      accepted_with_bound_tables_initial_roots_pullback_or_new_tree_output_hit
        [OF prefix_final bound])
    fix fr' f_fri_roots' f_final' dg' composition_fri_roots' final'
      rest' trace_tree composition_tree
    assume pull_header:
      "verifier_header_transcript ?s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
      and trace_created:
        "created_tree trace_table trace_tree final_state"
      and composition_created:
        "created_tree composition_table composition_tree final_state"
      and split:
        "(merkle_root_binds_table fr' trace_table prefix_state \<and>
          merkle_root_binds_table (hd composition_fri_roots')
            composition_table prefix_state) \<or>
          hash_map_new_output_hit
            (set_tree trace_tree \<union> set_tree composition_tree)
            prefix_state final_state"
    have pull_eq:
      "fr' = staged_trace_root data \<and>
       f_fri_roots' = staged_trace_fri_roots data \<and>
       f_final' = staged_trace_final data \<and>
       dg' = staged_degree data \<and>
       composition_fri_roots' = staged_composition_fri_roots data \<and>
       final' = staged_composition_final data \<and>
       rest' = List.concat (staged_query_chunks data)"
      using verifier_header_transcript_unique[OF pull_header staged_header]
        header_eq
      by simp
    from split show ?thesis
    proof
      assume binds:
        "merkle_root_binds_table fr' trace_table prefix_state \<and>
         merkle_root_binds_table (hd composition_fri_roots')
          composition_table prefix_state"
      have trace_len: "length trace_table = clength * scale"
        using bound unfolding accepted_with_bound_tables_def
          accepted_with_tables_def by simp
      have prefix_candidate:
        "trace_table \<in>
          alpha_prefix_trace_table_candidates prefix_state (fst prefix)"
        by (rule alpha_prefix_trace_table_candidateI[OF trace_len])
          (use binds pull_eq root_eq in simp)
      have prefix_bad:
        "staged_alphas data \<in>
          alpha_prefix_union_bad_sets prefix_state
            composition_trace_bad_alpha_space (fst prefix)"
        unfolding alpha_prefix_union_bad_sets_def
        using alphas_space prefix_candidate staged_bad by auto
      have
        "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space out"
        unfolding out_eq
          checked_staged_security_with_actual_alpha_prefix_bad_set_hit_def
          Let_def
        using prefix_bad by simp
      then show ?thesis by simp
    next
      assume tree_hit:
        "hash_map_new_output_hit
          (set_tree trace_tree \<union> set_tree composition_tree)
          prefix_state final_state"
      have
        "checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
          out"
        unfolding out_eq
          checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_def
          Let_def
        using verify_out bound pull_header trace_created composition_created
          tree_hit pull_eq
        by simp blast
      then show ?thesis by simp
    qed
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_bound_from_prefix_and_branch_tree:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and branch_tree_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
        adversary_initial_state \<le> T"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad)
      adversary_initial_state \<le> P + T"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?random =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad"
  let ?prefix =
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
      composition_trace_bad_alpha_space"
  let ?tree =
    "checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit"
  have "wp_event ?M ?random adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?prefix out \<or> ?tree out)
        adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_imp_prefix_or_branch_tree_on_support
        [OF wf controlled])
  also have "... \<le>
      wp_event ?M ?prefix adversary_initial_state +
      wp_event ?M ?tree adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> P + T"
    by (intro add_mono prefix_bound branch_tree_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_actual_alpha_prefix_branch_tree:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and branch_tree_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
        adversary_initial_state \<le> T"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le> P + T"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?degree =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_degree_bad"
  let ?random =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad"
  let ?bad =
    "checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_bad"
  have projected:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state =
     wp_event ?M ?bad adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection)
  have event_eq: "?bad = (\<lambda>out. ?degree out \<or> ?random out)"
    by (rule ext)
      (auto simp:
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        composition_bad_def split: option.splits prod.splits)
  have degree_false: "?degree = (\<lambda>out. False)"
    by (rule ext)
      (auto simp:
        checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        composition_degree_bad_false[OF spec_degree_wellformed_from_spec_query_margin]
        split: option.splits prod.splits)
  have degree_bound:
    "wp_event ?M ?degree adversary_initial_state \<le> 0"
    unfolding degree_false wp_event_def wp_def dist_expect_def by simp
  have random_bound:
    "wp_event ?M ?random adversary_initial_state \<le> P + T"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_randomization_bad_bound_from_prefix_and_branch_tree
        [OF wf controlled prefix_bound branch_tree_bound])
  have "wp_event ?M ?bad adversary_initial_state \<le>
      wp_event ?M ?degree adversary_initial_state +
      wp_event ?M ?random adversary_initial_state"
    unfolding event_eq by (rule wp_event_union_bound)
  also have "... \<le> 0 + (P + T)"
    by (intro add_mono degree_bound random_bound)
  finally show ?thesis
    unfolding projected by simp
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_actual_alpha_prefix_branch_tree_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and branch_tree_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
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
      T"
proof -
  let ?P =
    "composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  have transcript_bound:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound_from_budgets
        [OF wf controlled])
  have prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  have
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le> ?P + T"
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_actual_alpha_prefix_branch_tree
        [OF wf controlled prefix_bound branch_tree_bound])
  then show ?thesis
    by (simp add: add.assoc)
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_branch_split_side_events:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and root_pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
        adversary_initial_state \<le> RP"
    and target_bound:
      "\<And>packed attacker_state.
        Some (packed, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_with_alpha_prefix_program A)
              adversary_initial_state) \<Longrightarrow>
        concrete_transcript_target_error (staged_proof_transcript (snd packed))
          \<le> RV"
    and subtree_pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit
        adversary_initial_state \<le> SP"
    and subtree_verifier_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
        adversary_initial_state \<le> SV"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (RP + RV + SP + SV)"
proof -
  have branch_tree_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit
      adversary_initial_state \<le> RP + RV + SP + SV"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_branch_tree_output_hit_bound_from_preverifier_concrete_transcript_targets_and_split_subtree
        [OF wf controlled root_pre_bound target_bound subtree_pre_bound
          subtree_verifier_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_actual_alpha_prefix_branch_tree_and_budgets
        [OF wf controlled branch_tree_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_branch_split_side_events_and_transcript_budget:
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
    and subtree_verifier_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
        adversary_initial_state \<le> SV"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      (RP + staged_concrete_transcript_target_error_bound + SP + SV)"
proof -
  have target_bound:
    "\<And>packed attacker_state.
      Some (packed, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_with_alpha_prefix_program A)
            adversary_initial_state) \<Longrightarrow>
      concrete_transcript_target_error (staged_proof_transcript (snd packed))
        \<le> staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_transcript_with_alpha_prefix_program_concrete_transcript_target_error_bound
        [OF wf controlled])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_branch_split_side_events
        [OF wf controlled root_pre_bound target_bound subtree_pre_bound
          subtree_verifier_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_branch_split_side_events_and_transcript_budget_no_root_pre:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subtree_pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_preverifier_output_hit
        adversary_initial_state \<le> SP"
    and subtree_verifier_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_branch_tree_subtree_verifier_output_hit
        adversary_initial_state \<le> SV"
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
       staged_concrete_transcript_target_error_bound + SP + SV)"
proof -
  have root_pre_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_branch_transcript_root_preverifier_output_hit_bound
        [OF wf controlled])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_branch_split_side_events_and_transcript_budget
        [OF wf controlled root_pre_bound subtree_pre_bound
          subtree_verifier_bound])
qed

end

end
