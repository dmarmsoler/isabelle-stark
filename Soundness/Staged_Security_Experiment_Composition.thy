(*  Title:      Stark/Staged_Security_Experiment_Composition.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition
  imports
    Staged_Security_Experiment_Checked
    Staged_Security_Experiment_Alpha_Prequery
begin

text \<open>Prefix-fixed composition alpha targets for staged soundness.\<close>

context soundness
begin

definition checked_staged_after_alpha_prefix_program
  :: "'f staged_adversary \<Rightarrow>
      ('f \<times> 'f list \<times> 'f list \<times> 'f) \<Rightarrow>
      ('f staged_proof_data, 'f protocol_channel) state_monad"
  where
    "checked_staged_after_alpha_prefix_program A prefix =
      (case prefix of (fr, trace_roots, trace_bs, trace_final) \<Rightarrow>
        do {
          as \<leftarrow> staged_alpha_program (length spec);
          dg \<leftarrow> degree_stage A as;
          record_staged_message dg;
          let composition_rounds = ceil_log (to_nat dg + 1);
          assert (composition_rounds \<le> ceil_log (maxDegree + 1));
          (composition_roots, composition_bs) \<leftarrow>
            staged_composition_fri_program A dg 0 composition_rounds [];
          composition_final \<leftarrow>
            composition_final_stage A dg composition_bs;
          record_staged_message composition_final;
          query_chunks \<leftarrow>
            checked_staged_query_program A trace_roots composition_roots
              0 rounds;
          return
            \<lparr>staged_trace_root = fr,
             staged_trace_fri_roots = trace_roots,
             staged_trace_fri_challenges = trace_bs,
             staged_trace_final = trace_final,
             staged_alphas = as,
             staged_degree = dg,
             staged_composition_fri_roots = composition_roots,
             staged_composition_fri_challenges = composition_bs,
             staged_composition_final = composition_final,
             staged_query_chunks = query_chunks\<rparr>
        })"

lemma checked_staged_transcript_program_alpha_prefix_decomp:
  "checked_staged_transcript_program A =
    staged_alpha_prefix_program A \<bind>
      checked_staged_after_alpha_prefix_program A"
  unfolding checked_staged_transcript_program_def
    staged_alpha_prefix_program_def
    checked_staged_after_alpha_prefix_program_def Let_def
  by (simp add: sm_bind_assoc split_def split: prod.splits)

lemma sm_bind_get_ignore:
  "(get \<bind> (\<lambda>_. m)) = m"
  apply transfer
  apply (rule ext)
  apply (rule dist_inject[THEN iffD1])
  unfolding dist_bind.rep_eq dist_get_def
  apply (simp add: o_def dist_delta_dist)
  apply (subst map_bind_delta_left_state[where f="\<lambda>s. Some (s, s)"])
   apply (auto simp: bind_cont_map_def split: option.splits prod.splits)
  done

lemma checked_staged_after_alpha_prefix_program_alpha_list_bound_from_alpha_program:
  assumes alpha_bound:
    "wp_event (staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s \<le> C"
  shows
    "wp_event (checked_staged_after_alpha_prefix_program A prefix)
      (staged_transcript_alpha_list_hit B) s \<le> C"
proof -
  obtain fr trace_roots trace_bs trace_final where prefix_eq:
    "prefix = (fr, trace_roots, trace_bs, trace_final)"
    by (cases prefix) auto
  let ?P =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (as, _) \<Rightarrow> as \<in> B"
  have after_eq:
    "checked_staged_after_alpha_prefix_program A prefix =
      staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1)
             in assert
                (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  composition_rounds [] \<bind>
                  (\<lambda>(composition_roots, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                      (\<lambda>_. checked_staged_query_program A trace_roots
                        composition_roots 0 rounds \<bind>
                        (\<lambda>query_chunks.
                          return
                            \<lparr>staged_trace_root = fr,
                             staged_trace_fri_roots = trace_roots,
                             staged_trace_fri_challenges = trace_bs,
                             staged_trace_final = trace_final,
                             staged_alphas = as,
                             staged_degree = dg,
                             staged_composition_fri_roots =
                              composition_roots,
                             staged_composition_fri_challenges =
                              composition_bs,
                             staged_composition_final = composition_final,
                             staged_query_chunks =
                              query_chunks\<rparr>))))))))"
    unfolding checked_staged_after_alpha_prefix_program_def prefix_eq Let_def
    by simp
  show ?thesis
    unfolding after_eq staged_transcript_alpha_list_hit_def
  proof (rule wp_event_bind_bound_by_head_event[OF alpha_bound])
    show "(case None of None \<Rightarrow> False
          | Some (data, _) \<Rightarrow> staged_alphas data \<in> B) \<Longrightarrow>
      ?P None"
      by simp
  next
    fix as t out
    assume cont:
      "out \<in>
        set_dist
          (execute
            (degree_stage A as \<bind>
              (\<lambda>dg. record_staged_message dg \<bind>
                (\<lambda>_. let composition_rounds =
                  ceil_log (to_nat dg + 1)
                 in assert
                    (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      composition_rounds [] \<bind>
                      (\<lambda>(composition_roots, composition_bs).
                        composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                          (\<lambda>_. checked_staged_query_program A trace_roots
                            composition_roots 0 rounds \<bind>
                            (\<lambda>query_chunks.
                              return
                                \<lparr>staged_trace_root = fr,
                                 staged_trace_fri_roots = trace_roots,
                                 staged_trace_fri_challenges = trace_bs,
                                 staged_trace_final = trace_final,
                                 staged_alphas = as,
                                 staged_degree = dg,
                                 staged_composition_fri_roots =
                                  composition_roots,
                                 staged_composition_fri_challenges =
                                  composition_bs,
                                 staged_composition_final = composition_final,
                                 staged_query_chunks =
                                  query_chunks\<rparr>))))))))
          t)"
    and hit:
      "(case out of None \<Rightarrow> False
        | Some (data, _) \<Rightarrow> staged_alphas data \<in> B)"
    show "?P (Some (as, t))"
    proof (cases out)
      case None
      then show ?thesis using hit by simp
    next
      case (Some result)
      then obtain data u where out_eq: "out = Some (data, u)"
        by (cases result) simp
      have data_as: "staged_alphas data = as"
        using cont unfolding out_eq Let_def
        by (auto elim!: set_dist_bindE split: prod.splits)
      have "staged_alphas data \<in> B"
        using hit unfolding out_eq by simp
      then show ?thesis
        using data_as by simp
    qed
  qed
qed

lemma checked_staged_after_alpha_prefix_program_alpha_list_bound_from_path_fresh_or_prequery:
  assumes subset: "B \<subseteq> alpha_space"
  shows
    "wp_event (checked_staged_after_alpha_prefix_program A prefix)
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
    by (rule
        checked_staged_after_alpha_prefix_program_alpha_list_bound_from_alpha_program
        [OF alpha_bound])
qed

lemma checked_staged_after_alpha_prefix_program_alpha_list_bound_excluding_prequeried:
  assumes subset: "B \<subseteq> alpha_space"
  shows
    "wp_event (checked_staged_after_alpha_prefix_program A prefix)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (data, _) \<Rightarrow>
            staged_alphas data \<in> B \<and>
            \<not> alpha_vector_prequeried_in_state s
              (staged_alphas data) (length spec))
      s \<le> nnreal (card B) / nnreal (CARD('f) ^ length spec)"
proof -
  obtain fr trace_roots trace_bs trace_final where prefix_eq:
    "prefix = (fr, trace_roots, trace_bs, trace_final)"
    by (cases prefix) auto
  let ?P =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (as, _) \<Rightarrow>
          as \<in> B \<and>
          \<not> alpha_vector_prequeried_in_state s as (length spec)"
  have alpha_bound:
    "wp_event (staged_alpha_program (length spec))
      ?P s \<le> nnreal (card B) / nnreal (CARD('f) ^ length spec)"
    by (rule wp_staged_alpha_program_set_bound_excluding_prequeried
        [OF subset])
  have after_eq:
    "checked_staged_after_alpha_prefix_program A prefix =
      staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. let composition_rounds = ceil_log (to_nat dg + 1)
             in assert
                (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  composition_rounds [] \<bind>
                  (\<lambda>(composition_roots, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                      (\<lambda>_. checked_staged_query_program A trace_roots
                        composition_roots 0 rounds \<bind>
                        (\<lambda>query_chunks.
                          return
                            \<lparr>staged_trace_root = fr,
                             staged_trace_fri_roots = trace_roots,
                             staged_trace_fri_challenges = trace_bs,
                             staged_trace_final = trace_final,
                             staged_alphas = as,
                             staged_degree = dg,
                             staged_composition_fri_roots =
                              composition_roots,
                             staged_composition_fri_challenges =
                              composition_bs,
                             staged_composition_final = composition_final,
                             staged_query_chunks =
                              query_chunks\<rparr>))))))))"
    unfolding checked_staged_after_alpha_prefix_program_def prefix_eq Let_def
    by simp
  show ?thesis
    unfolding after_eq
  proof (rule wp_event_bind_bound_by_head_event[OF alpha_bound])
    show "(case None of None \<Rightarrow> False
          | Some (data, _) \<Rightarrow>
              staged_alphas data \<in> B \<and>
              \<not> alpha_vector_prequeried_in_state s
                (staged_alphas data) (length spec)) \<Longrightarrow>
      ?P None"
      by simp
  next
    fix as t out
    assume cont:
      "out \<in>
        set_dist
          (execute
            (degree_stage A as \<bind>
              (\<lambda>dg. record_staged_message dg \<bind>
                (\<lambda>_. let composition_rounds =
                  ceil_log (to_nat dg + 1)
                 in assert
                    (composition_rounds \<le> ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      composition_rounds [] \<bind>
                      (\<lambda>(composition_roots, composition_bs).
                        composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                          (\<lambda>_. checked_staged_query_program A trace_roots
                            composition_roots 0 rounds \<bind>
                            (\<lambda>query_chunks.
                              return
                                \<lparr>staged_trace_root = fr,
                                 staged_trace_fri_roots = trace_roots,
                                 staged_trace_fri_challenges = trace_bs,
                                 staged_trace_final = trace_final,
                                 staged_alphas = as,
                                 staged_degree = dg,
                                 staged_composition_fri_roots =
                                  composition_roots,
                                 staged_composition_fri_challenges =
                                  composition_bs,
                                 staged_composition_final = composition_final,
                                 staged_query_chunks =
                                  query_chunks\<rparr>))))))))
          t)"
      and hit:
        "(case out of None \<Rightarrow> False
          | Some (data, _) \<Rightarrow>
              staged_alphas data \<in> B \<and>
              \<not> alpha_vector_prequeried_in_state s
                (staged_alphas data) (length spec))"
    show "?P (Some (as, t))"
    proof (cases out)
      case None
      then show ?thesis using hit by simp
    next
      case (Some result)
      then obtain data u where out_eq: "out = Some (data, u)"
        by (cases result) simp
      have data_as: "staged_alphas data = as"
        using cont unfolding out_eq Let_def
        by (auto elim!: set_dist_bindE split: prod.splits)
      have "staged_alphas data \<in> B"
        "\<not> alpha_vector_prequeried_in_state s
          (staged_alphas data) (length spec)"
        using hit unfolding out_eq by simp_all
      then show ?thesis
        using data_as by simp
    qed
  qed
qed

definition checked_staged_transcript_with_alpha_prefix_program
  :: "'f staged_adversary \<Rightarrow>
      ((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
        'f protocol_channel) \<times> 'f staged_proof_data,
       'f protocol_channel) state_monad"
  where
    "checked_staged_transcript_with_alpha_prefix_program A =
      staged_alpha_prefix_program A \<bind>
        (\<lambda>prefix. get \<bind>
          (\<lambda>prefix_state.
            checked_staged_after_alpha_prefix_program A prefix \<bind>
              (\<lambda>data. return ((prefix, prefix_state), data))))"

definition checked_staged_security_experiment_with_actual_alpha_prefix_data_state
  :: "'f staged_adversary \<Rightarrow>
      ((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list,
       'f protocol_channel) state_monad"
  where
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A =
      checked_staged_transcript_with_alpha_prefix_program A \<bind>
        (\<lambda>packed. get \<bind>
          (\<lambda>s.
            put
              (verifier_state_from_adversary s
                (staged_proof_transcript (snd packed))) \<bind>
            (\<lambda>_.
              verify_monad \<bind>
                (\<lambda>result. return ((packed, s), result)))))"

lemma checked_staged_transcript_with_alpha_prefix_program_projection:
  "checked_staged_transcript_with_alpha_prefix_program A \<bind>
      (\<lambda>packed. return (snd packed)) =
    checked_staged_transcript_program A"
  unfolding checked_staged_transcript_with_alpha_prefix_program_def
    checked_staged_transcript_program_alpha_prefix_decomp
  by (simp add: sm_bind_assoc sm_bind_get_ignore)

lemma checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection:
  "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A \<bind>
      (\<lambda>x. return ((snd (fst (fst x)), snd (fst x)), snd x)) =
    checked_staged_security_experiment_with_data_state A"
proof -
  let ?K =
    "\<lambda>data. get \<bind>
      (\<lambda>s. put
        (verifier_state_from_adversary s
          (staged_proof_transcript data)) \<bind>
        (\<lambda>_. verify_monad \<bind>
          (\<lambda>result. return ((data, s), result))))"
  have
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A \<bind>
      (\<lambda>x. return ((snd (fst (fst x)), snd (fst x)), snd x)) =
     checked_staged_transcript_with_alpha_prefix_program A \<bind>
      (\<lambda>packed. ?K (snd packed))"
    unfolding
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    by (simp add: sm_bind_assoc split_def)
  also have "... =
      (checked_staged_transcript_with_alpha_prefix_program A \<bind>
        (\<lambda>packed. return (snd packed))) \<bind> ?K"
    by (simp add: sm_bind_assoc)
  also have "... =
      checked_staged_transcript_program A \<bind> ?K"
    unfolding checked_staged_transcript_with_alpha_prefix_program_projection
    by simp
  also have "... =
      checked_staged_security_experiment_with_data_state A"
    unfolding checked_staged_security_experiment_with_data_state_def by simp
  finally show ?thesis .
qed

lemma alpha_prefix_hash_extends_verifier_state_from_adversary_right:
  assumes ext: "s \<le> t"
  shows "s \<le> verifier_state_from_adversary t tr"
  using ext
  unfolding verifier_state_from_adversary_def less_eq_hash_ext_def
    less_eq_fmap_def
  by simp

definition alpha_prefix_trace_table_candidates
  :: "'f protocol_channel \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "alpha_prefix_trace_table_candidates prefix_state fr =
      {trace_table.
        length trace_table = clength * scale \<and>
        merkle_root_binds_table fr trace_table prefix_state}"

lemma alpha_prefix_trace_table_candidateI:
  assumes len: "length trace_table = clength * scale"
    and bind: "merkle_root_binds_table fr trace_table prefix_state"
  shows "trace_table \<in> alpha_prefix_trace_table_candidates prefix_state fr"
  using assms unfolding alpha_prefix_trace_table_candidates_def by simp

definition alpha_prefix_union_bad_sets
  :: "'f protocol_channel \<Rightarrow> ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      'f \<Rightarrow> 'f list set"
  where
    "alpha_prefix_union_bad_sets prefix_state bad_sets fr =
      {as \<in> alpha_space.
        \<exists>trace_table \<in>
          alpha_prefix_trace_table_candidates prefix_state fr.
          as \<in> bad_sets trace_table}"

definition checked_staged_transcript_actual_alpha_prefix_bad_set_hit
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
        'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_transcript_actual_alpha_prefix_bad_set_hit bad_sets out
      \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some ((((fr, _, _, _), prefix_state), data), _) \<Rightarrow>
          staged_alphas data \<in>
            alpha_prefix_union_bad_sets prefix_state bad_sets fr)"

definition checked_staged_transcript_actual_alpha_prefix_prequery_hit
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
        'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_transcript_actual_alpha_prefix_prequery_hit bad_sets out
      \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some ((((fr, _, _, _), prefix_state), data), _) \<Rightarrow>
          staged_alphas data \<in>
            alpha_prefix_union_bad_sets prefix_state bad_sets fr \<and>
          alpha_vector_prequeried_in_state prefix_state
            (staged_alphas data) (length spec))"

lemma checked_staged_transcript_actual_alpha_prefix_prequery_hit_imp_bad_set_hit:
  assumes
    "checked_staged_transcript_actual_alpha_prefix_prequery_hit bad_sets out"
  shows "checked_staged_transcript_actual_alpha_prefix_bad_set_hit bad_sets out"
  using assms
  unfolding checked_staged_transcript_actual_alpha_prefix_prequery_hit_def
    checked_staged_transcript_actual_alpha_prefix_bad_set_hit_def
  by (auto split: option.splits prod.splits)

definition checked_staged_transcript_actual_alpha_prefix_clean_fresh_bad_set_hit
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
        'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_transcript_actual_alpha_prefix_clean_fresh_bad_set_hit
      bad_sets out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((prefix, prefix_state), data), _) \<Rightarrow>
          \<not> hash_map_output_collision prefix_state \<and>
          staged_alphas data \<in>
            alpha_prefix_union_bad_sets prefix_state bad_sets (fst prefix) \<and>
          \<not> alpha_vector_prequeried_in_state prefix_state
            (staged_alphas data) (length spec))"

lemma checked_staged_transcript_actual_alpha_prefix_bad_set_hit_split:
  assumes
    "checked_staged_transcript_actual_alpha_prefix_bad_set_hit bad_sets out"
  shows
    "checked_staged_transcript_actual_alpha_prefix_clean_fresh_bad_set_hit
      bad_sets out \<or>
     checked_staged_transcript_actual_alpha_prefix_prequery_hit bad_sets out \<or>
     (case out of
        None \<Rightarrow> False
      | Some (((_, prefix_state), _), _) \<Rightarrow>
          hash_map_output_collision prefix_state)"
  using assms
  unfolding checked_staged_transcript_actual_alpha_prefix_bad_set_hit_def
    checked_staged_transcript_actual_alpha_prefix_clean_fresh_bad_set_hit_def
    checked_staged_transcript_actual_alpha_prefix_prequery_hit_def
  by (auto split: option.splits prod.splits)

lemma alpha_prefix_union_bad_sets_subset_alpha_space:
  "alpha_prefix_union_bad_sets prefix_state bad_sets fr \<subseteq> alpha_space"
  unfolding alpha_prefix_union_bad_sets_def by auto

lemma alpha_prefix_union_bad_sets_finite:
  "finite (alpha_prefix_union_bad_sets prefix_state bad_sets fr)"
  by (rule finite_subset[OF alpha_prefix_union_bad_sets_subset_alpha_space
        finite_alpha_space])

lemma alpha_prefix_union_bad_sets_fraction_bound_if_unique_candidate:
  fixes C :: prob
  assumes unique:
      "\<exists>trace_table.
        alpha_prefix_trace_table_candidates prefix_state fr \<subseteq>
          {trace_table}"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and bound:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space) \<le> C"
  shows
    "nnreal (card (alpha_prefix_union_bad_sets prefix_state bad_sets fr)) /
      nnreal (card alpha_space) \<le> C"
proof -
  from unique obtain trace_table where candidates:
    "alpha_prefix_trace_table_candidates prefix_state fr \<subseteq>
      {trace_table}"
    by blast
  have union_subset:
    "alpha_prefix_union_bad_sets prefix_state bad_sets fr \<subseteq>
      bad_sets trace_table"
    unfolding alpha_prefix_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (bad_sets trace_table)"
    by (rule finite_subset[OF subset finite_alpha_space])
  have card_le:
    "card (alpha_prefix_union_bad_sets prefix_state bad_sets fr) \<le>
      card (bad_sets trace_table)"
    by (rule card_mono[OF finite_bad union_subset])
  have "nnreal (card (alpha_prefix_union_bad_sets prefix_state bad_sets fr)) /
      nnreal (card alpha_space) \<le>
      nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma alpha_prefix_trace_table_candidates_unique_if_no_hash_collision:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
  shows
    "\<exists>trace_table.
      alpha_prefix_trace_table_candidates prefix_state fr \<subseteq>
        {trace_table}"
proof (cases "alpha_prefix_trace_table_candidates prefix_state fr = {}")
  case True
  then show ?thesis
    by blast
next
  case False
  then obtain trace_table where table_in:
    "trace_table \<in> alpha_prefix_trace_table_candidates prefix_state fr"
    by blast
  have table_len: "length trace_table = clength * scale"
    using table_in unfolding alpha_prefix_trace_table_candidates_def by simp
  have table_bind: "merkle_root_binds_table fr trace_table prefix_state"
    using table_in unfolding alpha_prefix_trace_table_candidates_def by simp
  have subset_single:
    "alpha_prefix_trace_table_candidates prefix_state fr \<subseteq>
      {trace_table}"
  proof
    fix trace_table'
    assume table'_in:
      "trace_table' \<in> alpha_prefix_trace_table_candidates prefix_state fr"
    have table'_len: "length trace_table' = clength * scale"
      using table'_in unfolding alpha_prefix_trace_table_candidates_def
      by simp
    have table'_bind:
      "merkle_root_binds_table fr trace_table' prefix_state"
      using table'_in unfolding alpha_prefix_trace_table_candidates_def
      by simp
    have "trace_table' = trace_table"
      by (rule merkle_root_binds_same_length_tables_unique_if_no_hash_collision
          [OF table'_bind table_bind])
        (use table'_len table_len clean in simp_all)
    then show "trace_table' \<in> {trace_table}"
      by simp
  qed
  then show ?thesis by blast
qed

lemma composition_alpha_prefix_union_fraction_bound_if_no_hash_collision:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
  shows
    "nnreal
      (card
        (alpha_prefix_union_bad_sets prefix_state
          composition_trace_bad_alpha_space fr)) /
      nnreal (card alpha_space) \<le> composition_error_bound"
  by (rule alpha_prefix_union_bad_sets_fraction_bound_if_unique_candidate)
    (rule alpha_prefix_trace_table_candidates_unique_if_no_hash_collision
        [OF clean],
      rule composition_trace_bad_alpha_space_subset_alpha_space,
      rule composition_trace_bad_alpha_space_fraction_bound_alpha_space)

lemma alpha_prefix_union_bad_sets_card_bound_if_unique_candidate:
  assumes unique:
      "\<exists>trace_table.
        alpha_prefix_trace_table_candidates prefix_state fr \<subseteq>
          {trace_table}"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and bound:
      "\<And>trace_table. card (bad_sets trace_table) \<le> C"
  shows
    "card (alpha_prefix_union_bad_sets prefix_state bad_sets fr) \<le> C"
proof -
  from unique obtain trace_table where candidates:
    "alpha_prefix_trace_table_candidates prefix_state fr \<subseteq>
      {trace_table}"
    by blast
  have union_subset:
    "alpha_prefix_union_bad_sets prefix_state bad_sets fr \<subseteq>
      bad_sets trace_table"
    unfolding alpha_prefix_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (bad_sets trace_table)"
    by (rule finite_subset[OF subset finite_alpha_space])
  have "card (alpha_prefix_union_bad_sets prefix_state bad_sets fr) \<le>
      card (bad_sets trace_table)"
    by (rule card_mono[OF finite_bad union_subset])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma composition_alpha_prefix_union_card_bound_if_no_hash_collision:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
  shows
    "card
      (alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space fr) \<le>
      (if length spec = 0 then 0 else CARD('f) ^ (length spec - 1))"
  by (rule alpha_prefix_union_bad_sets_card_bound_if_unique_candidate)
    (rule alpha_prefix_trace_table_candidates_unique_if_no_hash_collision
        [OF clean],
      rule composition_trace_bad_alpha_space_subset_alpha_space,
      rule composition_trace_bad_alpha_space_card_bound)

lemma checked_staged_transcript_with_alpha_prefix_clean_fresh_composition_bound:
  shows
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_clean_fresh_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> composition_error_bound"
  unfolding checked_staged_transcript_with_alpha_prefix_program_def
proof (rule wp_event_bind_bound_by_cont)
  show
    "\<not> checked_staged_transcript_actual_alpha_prefix_clean_fresh_bad_set_hit
      composition_trace_bad_alpha_space None"
    unfolding
      checked_staged_transcript_actual_alpha_prefix_clean_fresh_bad_set_hit_def
    by simp
next
  fix prefix prefix_state
  assume prefix_out:
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A) adversary_initial_state)"
  obtain fr trace_roots trace_bs trace_final where prefix_eq:
    "prefix = (fr, trace_roots, trace_bs, trace_final)"
    by (cases prefix) auto
  let ?B =
    "alpha_prefix_union_bad_sets prefix_state
      composition_trace_bad_alpha_space fr"
  let ?Q =
    "checked_staged_transcript_actual_alpha_prefix_clean_fresh_bad_set_hit
      composition_trace_bad_alpha_space"
  let ?E =
    "\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (data, _) \<Rightarrow>
        \<not> hash_map_output_collision prefix_state \<and>
        staged_alphas data \<in> ?B \<and>
        \<not> alpha_vector_prequeried_in_state prefix_state
          (staged_alphas data) (length spec)"
  have get_eq:
    "wp_event
      (get \<bind>
        (\<lambda>prefix_state'.
          checked_staged_after_alpha_prefix_program A prefix \<bind>
            (\<lambda>data. return ((prefix, prefix_state'), data))))
      ?Q prefix_state =
      wp_event
        (checked_staged_after_alpha_prefix_program A prefix \<bind>
          (\<lambda>data. return ((prefix, prefix_state), data)))
        ?Q
        prefix_state"
    unfolding wp_event_def by (simp add: wpsimps)
  have return_eq:
    "wp_event
      (checked_staged_after_alpha_prefix_program A prefix \<bind>
        (\<lambda>data. return ((prefix, prefix_state), data)))
      ?Q prefix_state =
      wp_event (checked_staged_after_alpha_prefix_program A prefix) ?E
        prefix_state"
    apply (subst wp_event_bind_return_map)
    unfolding
      checked_staged_transcript_actual_alpha_prefix_clean_fresh_bad_set_hit_def
      prefix_eq
    by (simp split: option.splits prod.splits)
  have cont_eq:
    "wp_event
      (get \<bind>
        (\<lambda>prefix_state'.
          checked_staged_after_alpha_prefix_program A prefix \<bind>
            (\<lambda>data. return ((prefix, prefix_state'), data))))
      ?Q prefix_state =
      wp_event (checked_staged_after_alpha_prefix_program A prefix) ?E
        prefix_state"
    using get_eq return_eq by simp
  show
    "wp_event
      (get \<bind>
        (\<lambda>prefix_state.
          checked_staged_after_alpha_prefix_program A prefix \<bind>
            (\<lambda>data. return ((prefix, prefix_state), data))))
      ?Q prefix_state \<le> composition_error_bound"
  proof (cases "hash_map_output_collision prefix_state")
    case True
    have zero:
      "wp_event (checked_staged_after_alpha_prefix_program A prefix) ?E
        prefix_state = 0"
    proof -
      have indicator_zero:
        "(\<lambda>x. if ?E x then 1 else 0 :: prob) = (\<lambda>_. 0)"
        using True
        by (auto simp: fun_eq_iff split: option.splits prod.splits)
      show ?thesis
        unfolding wp_event_def indicator_zero wp_def by simp
    qed
    show ?thesis
      unfolding cont_eq zero by simp
  next
    case False
    have subset: "?B \<subseteq> alpha_space"
      by (rule alpha_prefix_union_bad_sets_subset_alpha_space)
    have suffix_bound:
      "wp_event (checked_staged_after_alpha_prefix_program A prefix)
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some (data, _) \<Rightarrow>
              staged_alphas data \<in> ?B \<and>
              \<not> alpha_vector_prequeried_in_state prefix_state
                (staged_alphas data) (length spec))
        prefix_state \<le>
        nnreal (card ?B) / nnreal (CARD('f) ^ length spec)"
      by (rule
          checked_staged_after_alpha_prefix_program_alpha_list_bound_excluding_prequeried
          [OF subset])
    have clean_bound:
      "nnreal (card ?B) / nnreal (CARD('f) ^ length spec) \<le>
        composition_error_bound"
      using composition_alpha_prefix_union_fraction_bound_if_no_hash_collision
        [OF False, of fr]
      by (simp add: card_alpha_space)
    have event_eq:
      "?E =
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some (data, _) \<Rightarrow>
              staged_alphas data \<in> ?B \<and>
              \<not> alpha_vector_prequeried_in_state prefix_state
                (staged_alphas data) (length spec))"
      using False
      by (auto simp: fun_eq_iff split: option.splits prod.splits)
    show ?thesis
      unfolding cont_eq event_eq
      by (rule order_trans[OF suffix_bound clean_bound])
  qed
qed

lemma alpha_prefix_composition_vector_key_relation_fiber_bound_if_no_hash_collision:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
  shows
    "card
      {y. alpha_vector_key_relation prefix_state
        (alpha_prefix_union_bad_sets prefix_state
          composition_trace_bad_alpha_space fr)
        (length spec) x y}
      \<le> (if length spec = 0 then 0 else CARD('f) ^ (length spec - 1)) *
        length spec"
proof -
  have finite_bad:
    "finite
      (alpha_prefix_union_bad_sets prefix_state
        composition_trace_bad_alpha_space fr)"
    by (rule alpha_prefix_union_bad_sets_finite)
  have relation_bound:
    "card
      {y. alpha_vector_key_relation prefix_state
        (alpha_prefix_union_bad_sets prefix_state
          composition_trace_bad_alpha_space fr)
        (length spec) x y}
      \<le>
      card
        (alpha_prefix_union_bad_sets prefix_state
          composition_trace_bad_alpha_space fr) *
        length spec"
    by (rule alpha_vector_key_relation_fiber_card_bound[OF finite_bad])
  also have "... \<le>
      (if length spec = 0 then 0 else CARD('f) ^ (length spec - 1)) *
        length spec"
  proof (cases "length spec = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have "card
        (alpha_prefix_union_bad_sets prefix_state
          composition_trace_bad_alpha_space fr)
        \<le> CARD('f) ^ (length spec - 1)"
      using composition_alpha_prefix_union_card_bound_if_no_hash_collision
        [OF clean] False
      by simp
    then show ?thesis
      using False
      by (intro mult_right_mono) simp_all
  qed
  finally show ?thesis .
qed

definition checked_staged_security_with_data_state_alpha_prefix_bad_set_hit
  :: "'f staged_adversary \<Rightarrow> ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
      bad_sets out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, _), _), _) \<Rightarrow>
          (\<exists>prefix prefix_state.
            Some (prefix, prefix_state) \<in>
              set_dist
                (execute (staged_alpha_prefix_program A)
                  adversary_initial_state) \<and>
            staged_trace_root data = fst prefix \<and>
            staged_trace_fri_roots data = fst (snd prefix) \<and>
            staged_trace_fri_challenges data = fst (snd (snd prefix)) \<and>
            staged_trace_final data = snd (snd (snd prefix)) \<and>
            staged_alphas data \<in>
              alpha_prefix_union_bad_sets prefix_state bad_sets
                (staged_trace_root data)))"

definition checked_staged_transcript_alpha_prefix_prequery_hit
  :: "'f staged_adversary \<Rightarrow> ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      ('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_transcript_alpha_prefix_prequery_hit A bad_sets out
      \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (data, _) \<Rightarrow>
          (\<exists>prefix prefix_state.
            Some (prefix, prefix_state) \<in>
              set_dist
                (execute (staged_alpha_prefix_program A)
                  adversary_initial_state) \<and>
            staged_trace_root data = fst prefix \<and>
            staged_trace_fri_roots data = fst (snd prefix) \<and>
            staged_trace_fri_challenges data = fst (snd (snd prefix)) \<and>
            staged_trace_final data = snd (snd (snd prefix)) \<and>
            staged_alphas data \<in>
              alpha_prefix_union_bad_sets prefix_state bad_sets
                (staged_trace_root data) \<and>
            alpha_vector_prequeried_in_state prefix_state
              (staged_alphas data) (length spec)))"

definition checked_staged_transcript_alpha_prefix_bad_set_hit
  :: "'f staged_adversary \<Rightarrow> ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      ('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_transcript_alpha_prefix_bad_set_hit A bad_sets out
      \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (data, _) \<Rightarrow>
          (\<exists>prefix prefix_state.
            Some (prefix, prefix_state) \<in>
              set_dist
                (execute (staged_alpha_prefix_program A)
                  adversary_initial_state) \<and>
            staged_trace_root data = fst prefix \<and>
            staged_trace_fri_roots data = fst (snd prefix) \<and>
            staged_trace_fri_challenges data = fst (snd (snd prefix)) \<and>
            staged_trace_final data = snd (snd (snd prefix)) \<and>
            staged_alphas data \<in>
              alpha_prefix_union_bad_sets prefix_state bad_sets
                (staged_trace_root data)))"

lemma checked_staged_transcript_alpha_prefix_prequery_hit_imp_bad_set_hit:
  assumes hit:
    "checked_staged_transcript_alpha_prefix_prequery_hit A bad_sets out"
  shows "checked_staged_transcript_alpha_prefix_bad_set_hit A bad_sets out"
  using hit
  unfolding checked_staged_transcript_alpha_prefix_prequery_hit_def
    checked_staged_transcript_alpha_prefix_bad_set_hit_def
  by (auto split: option.splits prod.splits)

lemma checked_staged_transcript_alpha_prefix_prequery_hitE:
  assumes hit:
    "checked_staged_transcript_alpha_prefix_prequery_hit A bad_sets
      (Some (data, attacker_state))"
  obtains prefix prefix_state where
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A) adversary_initial_state)"
    "staged_trace_root data = fst prefix"
    "staged_trace_fri_roots data = fst (snd prefix)"
    "staged_trace_fri_challenges data = fst (snd (snd prefix))"
    "staged_trace_final data = snd (snd (snd prefix))"
    "staged_alphas data \<in>
      alpha_prefix_union_bad_sets prefix_state bad_sets
        (staged_trace_root data)"
    "alpha_vector_prequeried_in_state prefix_state
      (staged_alphas data) (length spec)"
    "hash_relation_hit
      (alpha_vector_key_relation prefix_state
        (alpha_prefix_union_bad_sets prefix_state bad_sets
          (staged_trace_root data))
        (length spec))
      adversary_initial_state prefix_state"
proof -
  from hit obtain prefix prefix_state where
    prefix_out:
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
    and member:
      "staged_alphas data \<in>
        alpha_prefix_union_bad_sets prefix_state bad_sets
          (staged_trace_root data)"
    and prequeried:
      "alpha_vector_prequeried_in_state prefix_state
        (staged_alphas data) (length spec)"
    unfolding checked_staged_transcript_alpha_prefix_prequery_hit_def
    by auto
  have relation_hit:
    "hash_relation_hit
      (alpha_vector_key_relation prefix_state
        (alpha_prefix_union_bad_sets prefix_state bad_sets
          (staged_trace_root data))
        (length spec))
      adversary_initial_state prefix_state"
    by (rule alpha_vector_prequeried_in_state_imp_hash_relation_hit_empty_initial
        [OF prequeried member])
      simp
  show ?thesis
    by (rule that[OF prefix_out root_eq trace_roots_eq trace_bs_eq
          trace_final_eq member prequeried relation_hit])
qed

definition staged_alpha_prefix_dynamic_prequery_hit
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_alpha_prefix_dynamic_prequery_hit bad_sets out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some ((fr, _), prefix_state) \<Rightarrow>
          (\<exists>as \<in> alpha_prefix_union_bad_sets prefix_state bad_sets fr.
            alpha_vector_prequeried_in_state prefix_state as
              (length spec)))"

definition staged_alpha_prefix_dynamic_prequery_relation
  :: "'f staged_adversary \<Rightarrow> 'f protocol_channel \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "staged_alpha_prefix_dynamic_prequery_relation A s bad_sets x y
      \<longleftrightarrow>
      (\<exists>fr trace_roots trace_bs trace_final prefix_state as i.
        Some ((fr, trace_roots, trace_bs, trace_final), prefix_state) \<in>
          set_dist (execute (staged_alpha_prefix_program A) s) \<and>
        as \<in> alpha_prefix_union_bad_sets prefix_state bad_sets fr \<and>
        i < length spec \<and>
        i < length as \<and>
        x = alpha_challenge_key_at prefix_state i as \<and>
        y = as ! i)"

lemma staged_alpha_prefix_dynamic_prequery_hit_imp_relation_hit:
  assumes empty: "HashMap s = fmempty"
    and support:
      "Some ((fr, trace_roots, trace_bs, trace_final), prefix_state) \<in>
        set_dist (execute (staged_alpha_prefix_program A) s)"
    and hit:
      "staged_alpha_prefix_dynamic_prequery_hit bad_sets
        (Some ((fr, trace_roots, trace_bs, trace_final), prefix_state))"
  shows
    "hash_relation_hit_event
      (staged_alpha_prefix_dynamic_prequery_relation A s bad_sets)
      s (Some ((fr, trace_roots, trace_bs, trace_final), prefix_state))"
proof -
  from hit obtain as i where member:
      "as \<in> alpha_prefix_union_bad_sets prefix_state bad_sets fr"
    and i_bound: "i < length spec"
    and i_len: "i < length as"
    and lookup:
      "fmlookup (HashMap prefix_state)
        (alpha_challenge_key_at prefix_state i as) = Some (as ! i)"
    unfolding staged_alpha_prefix_dynamic_prequery_hit_def
      alpha_vector_prequeried_in_state_def
    by auto
  have initial_none:
    "fmlookup (HashMap s) (alpha_challenge_key_at prefix_state i as) =
      None"
    using empty by simp
  have relation:
    "staged_alpha_prefix_dynamic_prequery_relation A s bad_sets
      (alpha_challenge_key_at prefix_state i as) (as ! i)"
    unfolding staged_alpha_prefix_dynamic_prequery_relation_def
    using support member i_bound i_len by blast
  have hit_relation:
    "hash_relation_hit
      (staged_alpha_prefix_dynamic_prequery_relation A s bad_sets)
      s prefix_state"
    unfolding hash_relation_hit_def
    by (intro exI[of _ "alpha_challenge_key_at prefix_state i as"]
        exI[of _ "as ! i"] conjI)
      (use initial_none lookup relation in simp_all)
  show ?thesis
    unfolding hash_relation_hit_event_def using hit_relation by simp
qed

lemma staged_alpha_prefix_dynamic_prequery_hit_bound_by_relation_hit:
  assumes empty: "HashMap s = fmempty"
  shows
    "wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_dynamic_prequery_hit bad_sets) s \<le>
     wp_event (staged_alpha_prefix_program A)
      (hash_relation_hit_event
        (staged_alpha_prefix_dynamic_prequery_relation A s bad_sets) s) s"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in> set_dist (execute (staged_alpha_prefix_program A) s)"
    and prehit: "staged_alpha_prefix_dynamic_prequery_hit bad_sets out"
  show
    "hash_relation_hit_event
      (staged_alpha_prefix_dynamic_prequery_relation A s bad_sets)
      s out"
  proof (cases out)
    case None
    then show ?thesis
      using prehit unfolding staged_alpha_prefix_dynamic_prequery_hit_def
      by simp
  next
    case (Some packed)
    then obtain fr trace_roots trace_bs trace_final prefix_state
      where out_eq:
        "out =
          Some ((fr, trace_roots, trace_bs, trace_final), prefix_state)"
      by (cases packed, auto split: prod.splits)
    show ?thesis
      unfolding out_eq
      by (rule staged_alpha_prefix_dynamic_prequery_hit_imp_relation_hit
          [OF empty])
        (use support prehit out_eq in simp_all)
  qed
qed

lemma staged_alpha_prefix_dynamic_prequery_relation_fiber_bound_size:
  "card
    {y. staged_alpha_prefix_dynamic_prequery_relation A s bad_sets x y}
    \<le> size"
proof -
  have subset:
    "{y. staged_alpha_prefix_dynamic_prequery_relation A s bad_sets x y}
      \<subseteq> (UNIV :: 'f set)"
    by simp
  have finite_field: "finite (UNIV :: 'f set)"
    by simp
  have "card
      {y. staged_alpha_prefix_dynamic_prequery_relation A s bad_sets x y}
      \<le> card (UNIV :: 'f set)"
    by (rule card_mono[OF finite_field subset])
  also have "... = size"
    using size_card by simp
  finally show ?thesis .
qed

lemma staged_alpha_prefix_dynamic_prequery_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_dynamic_prequery_hit bad_sets)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  have prehit_le_relation:
    "wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_dynamic_prequery_hit bad_sets)
      adversary_initial_state \<le>
     wp_event (staged_alpha_prefix_program A)
      (hash_relation_hit_event
        (staged_alpha_prefix_dynamic_prequery_relation A
          adversary_initial_state bad_sets)
        adversary_initial_state)
      adversary_initial_state"
    by (rule staged_alpha_prefix_dynamic_prequery_hit_bound_by_relation_hit)
      (simp add: adversary_initial_state_def)
  also have "... \<le>
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
  proof -
    have program:
      "hash_relation_program
        (staged_alpha_prefix_dynamic_prequery_relation A
          adversary_initial_state bad_sets)
        size (staged_alpha_search_queries budgets 0)
        (staged_alpha_prefix_program A)"
      by (rule hash_relation_program_staged_alpha_prefix_program
          [OF wf controlled])
        (rule staged_alpha_prefix_dynamic_prequery_relation_fiber_bound_size)
    show ?thesis
      using program
      unfolding hash_relation_program_def hash_relation_budget_def
        staged_phase_relation_error_def
      by blast
  qed
  finally show ?thesis .
qed

definition checked_staged_transcript_actual_alpha_prefix_collision_hit
  :: "(((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
        'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_transcript_actual_alpha_prefix_collision_hit out
      \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((_, prefix_state), _), _) \<Rightarrow>
          hash_map_output_collision prefix_state)"

lemma checked_staged_transcript_actual_alpha_prefix_bad_set_hit_split_events:
  assumes
    "checked_staged_transcript_actual_alpha_prefix_bad_set_hit bad_sets out"
  shows
    "checked_staged_transcript_actual_alpha_prefix_clean_fresh_bad_set_hit
      bad_sets out \<or>
     checked_staged_transcript_actual_alpha_prefix_prequery_hit bad_sets out \<or>
     checked_staged_transcript_actual_alpha_prefix_collision_hit out"
  using checked_staged_transcript_actual_alpha_prefix_bad_set_hit_split
    [OF assms]
  unfolding checked_staged_transcript_actual_alpha_prefix_collision_hit_def
  by (auto split: option.splits prod.splits)

lemma checked_staged_transcript_with_alpha_prefix_prequery_bound:
  shows
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_prequery_hit bad_sets)
      adversary_initial_state \<le>
     wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_dynamic_prequery_hit bad_sets)
      adversary_initial_state"
  unfolding checked_staged_transcript_with_alpha_prefix_program_def
proof (rule wp_event_bind_bound_by_head_event)
  show
    "wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_dynamic_prequery_hit bad_sets)
      adversary_initial_state \<le>
     wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_dynamic_prequery_hit bad_sets)
      adversary_initial_state"
    by simp
next
  show
    "checked_staged_transcript_actual_alpha_prefix_prequery_hit
      bad_sets None \<Longrightarrow>
     staged_alpha_prefix_dynamic_prequery_hit bad_sets None"
    unfolding checked_staged_transcript_actual_alpha_prefix_prequery_hit_def
      staged_alpha_prefix_dynamic_prequery_hit_def
    by simp
next
  fix prefix prefix_state out
  assume prefix_out:
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A) adversary_initial_state)"
    and cont:
    "out \<in>
      set_dist
        (execute
          (get \<bind>
            (\<lambda>prefix_state.
              checked_staged_after_alpha_prefix_program A prefix \<bind>
              (\<lambda>data. return ((prefix, prefix_state), data))))
          prefix_state)"
    and hit:
    "checked_staged_transcript_actual_alpha_prefix_prequery_hit
      bad_sets out"
  obtain fr trace_roots trace_bs trace_final where prefix_eq:
    "prefix = (fr, trace_roots, trace_bs, trace_final)"
    by (cases prefix) auto
  from hit cont show
    "staged_alpha_prefix_dynamic_prequery_hit bad_sets
      (Some (prefix, prefix_state))"
    unfolding checked_staged_transcript_actual_alpha_prefix_prequery_hit_def
      staged_alpha_prefix_dynamic_prequery_hit_def prefix_eq
    by (auto elim!: set_dist_bindE split: option.splits prod.splits)
qed

lemma checked_staged_transcript_with_alpha_prefix_collision_bound:
  shows
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      checked_staged_transcript_actual_alpha_prefix_collision_hit
      adversary_initial_state \<le>
     wp_event (staged_alpha_prefix_program A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state"
  unfolding checked_staged_transcript_with_alpha_prefix_program_def
proof (rule wp_event_bind_bound_by_head_event)
  show
    "wp_event (staged_alpha_prefix_program A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le>
     wp_event (staged_alpha_prefix_program A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state"
    by simp
next
  show
    "checked_staged_transcript_actual_alpha_prefix_collision_hit None \<Longrightarrow>
     hash_new_collision_event adversary_initial_state None"
    unfolding checked_staged_transcript_actual_alpha_prefix_collision_hit_def
      hash_new_collision_event_def
    by simp
next
  fix prefix prefix_state out
  assume prefix_out:
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A) adversary_initial_state)"
    and cont:
    "out \<in>
      set_dist
        (execute
          (get \<bind>
            (\<lambda>prefix_state.
              checked_staged_after_alpha_prefix_program A prefix \<bind>
              (\<lambda>data. return ((prefix, prefix_state), data))))
          prefix_state)"
    and hit:
    "checked_staged_transcript_actual_alpha_prefix_collision_hit out"
  have collision: "hash_map_output_collision prefix_state"
    using hit cont
    unfolding checked_staged_transcript_actual_alpha_prefix_collision_hit_def
    by (auto elim!: set_dist_bindE split: option.splits prod.splits)
  show
    "hash_new_collision_event adversary_initial_state
      (Some (prefix, prefix_state))"
    using collision adversary_initial_state_no_output_collision
    unfolding hash_new_collision_event_def hash_map_new_output_collision_def
    by simp
qed

lemma checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound:
  shows
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      composition_error_bound +
      wp_event (staged_alpha_prefix_program A)
        (staged_alpha_prefix_dynamic_prequery_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state +
      wp_event (staged_alpha_prefix_program A)
        (hash_new_collision_event adversary_initial_state)
        adversary_initial_state"
proof -
  let ?m = "checked_staged_transcript_with_alpha_prefix_program A"
  let ?bad =
    "checked_staged_transcript_actual_alpha_prefix_bad_set_hit
      composition_trace_bad_alpha_space"
  let ?clean =
    "checked_staged_transcript_actual_alpha_prefix_clean_fresh_bad_set_hit
      composition_trace_bad_alpha_space"
  let ?pre =
    "checked_staged_transcript_actual_alpha_prefix_prequery_hit
      composition_trace_bad_alpha_space"
  let ?coll = checked_staged_transcript_actual_alpha_prefix_collision_hit
  have bad_le_split:
    "wp_event ?m ?bad adversary_initial_state \<le>
      wp_event ?m (\<lambda>out. ?clean out \<or> ?pre out \<or> ?coll out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_transcript_actual_alpha_prefix_bad_set_hit_split_events)
  also have "... \<le>
      wp_event ?m ?clean adversary_initial_state +
      wp_event ?m ?pre adversary_initial_state +
      wp_event ?m ?coll adversary_initial_state"
  proof -
    have "... \<le>
        wp_event ?m ?clean adversary_initial_state +
        wp_event ?m (\<lambda>out. ?pre out \<or> ?coll out)
          adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le>
        wp_event ?m ?clean adversary_initial_state +
        (wp_event ?m ?pre adversary_initial_state +
         wp_event ?m ?coll adversary_initial_state)"
      by (intro add_mono order.refl wp_event_union_bound)
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  also have "... \<le>
      composition_error_bound +
      wp_event (staged_alpha_prefix_program A)
        (staged_alpha_prefix_dynamic_prequery_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state +
      wp_event (staged_alpha_prefix_program A)
        (hash_new_collision_event adversary_initial_state)
        adversary_initial_state"
    by (intro add_mono
        checked_staged_transcript_with_alpha_prefix_clean_fresh_composition_bound
        checked_staged_transcript_with_alpha_prefix_prequery_bound
        checked_staged_transcript_with_alpha_prefix_collision_bound)
  finally show ?thesis .
qed

lemma checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
proof -
  have prequery_bound:
    "wp_event (staged_alpha_prefix_program A)
      (staged_alpha_prefix_dynamic_prequery_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule staged_alpha_prefix_dynamic_prequery_hit_bound
        [OF wf controlled])
  have collision_budget:
    "hash_collision_budget
      (staged_alpha_search_queries budgets 0)
      (staged_alpha_prefix_program A)"
    by (rule hash_collision_budget_staged_alpha_prefix_program
        [OF wf controlled])
  have collision_bound:
    "wp_event (staged_alpha_prefix_program A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
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
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0)"
      by simp
    finally show ?thesis .
  qed
  have
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      composition_error_bound +
      wp_event (staged_alpha_prefix_program A)
        (staged_alpha_prefix_dynamic_prequery_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state +
      wp_event (staged_alpha_prefix_program A)
        (hash_new_collision_event adversary_initial_state)
        adversary_initial_state"
    by (rule checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound)
  also have "... \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
    by (intro add_mono order.refl prequery_bound collision_bound)
  finally show ?thesis .
qed

definition checked_staged_security_with_actual_alpha_prefix_bad_set_hit
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
      bad_sets out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, _) \<Rightarrow>
          (let packed = fst (fst x);
               prefix = fst (fst packed);
               prefix_state = snd (fst packed);
               data = snd packed
           in staged_alphas data \<in>
            alpha_prefix_union_bad_sets prefix_state bad_sets (fst prefix)))"

definition checked_staged_security_with_actual_alpha_prefix_header_supported_bad_set_hit
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_actual_alpha_prefix_header_supported_bad_set_hit
      bad_sets out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (x, _) \<Rightarrow>
          (let packed = fst (fst x);
               data = snd packed;
               attacker_state = snd (fst x)
           in staged_alphas data \<in>
            alpha_header_supported_union_bad_sets
              (verifier_state_from_adversary attacker_state
                (staged_proof_transcript data))
              bad_sets
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)))"

definition checked_staged_security_with_actual_alpha_prefix_tree_output_hit
  :: "(((((('f \<times> 'f list \<times> 'f list \<times> 'f) \<times>
          'f protocol_channel) \<times> 'f staged_proof_data) \<times>
        'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_actual_alpha_prefix_tree_output_hit out
      \<longleftrightarrow>
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
           in \<exists>result final_state trace_table composition_table as
              query_idxs dg composition_fri_roots final rest trace_tree
              composition_tree.
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

lemma checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript:
  assumes transcript_bound:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit bad_sets)
      adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit bad_sets)
      adversary_initial_state \<le> C"
  unfolding
    checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
proof (rule wp_event_bind_bound_by_head_event[OF transcript_bound])
  show
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
      bad_sets None \<Longrightarrow>
     checked_staged_transcript_actual_alpha_prefix_bad_set_hit bad_sets None"
    unfolding checked_staged_security_with_actual_alpha_prefix_bad_set_hit_def
      checked_staged_transcript_actual_alpha_prefix_bad_set_hit_def
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
      "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        bad_sets out"
  show
    "checked_staged_transcript_actual_alpha_prefix_bad_set_hit bad_sets
      (Some (packed, attacker_state))"
    using cont hit
    unfolding checked_staged_security_with_actual_alpha_prefix_bad_set_hit_def
      checked_staged_transcript_actual_alpha_prefix_bad_set_hit_def
    by (auto elim!: set_dist_bindE split: option.splits prod.splits)
qed

lemma checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit_actual_projection:
  "wp_event (checked_staged_security_experiment_with_data_state A)
    (checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
      bad_sets)
    adversary_initial_state =
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_header_supported_bad_set_hit
      bad_sets)
    adversary_initial_state"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
        bad_sets)
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
        \<bind> (\<lambda>x. return (?project x)))
      (checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
        bad_sets)
      adversary_initial_state"
    using
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
      [of A]
    by simp
  also have "... =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. case out of
        None \<Rightarrow>
          checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
            bad_sets None
      | Some (x, t) \<Rightarrow>
          checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
            bad_sets (Some (?project x, t)))
      adversary_initial_state"
    by (rule wp_event_bind_return_map)
  also have "... =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_header_supported_bad_set_hit
        bad_sets)
      adversary_initial_state"
    unfolding
      checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit_def
      checked_staged_security_with_actual_alpha_prefix_header_supported_bad_set_hit_def
    apply (rule arg_cong[where
        f="\<lambda>P. wp_event
          (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
          P adversary_initial_state"])
    apply (rule ext)
    apply (simp add: Let_def split: option.splits prod.splits)
    done
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_tree_output_hitI:
  assumes verify_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
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
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        as dg composition_fri_roots final rest"
    and trace_created: "created_tree trace_table trace_tree final_state"
    and composition_created:
      "created_tree composition_table composition_tree final_state"
    and tree_hit:
      "hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
  shows
    "checked_staged_security_with_actual_alpha_prefix_tree_output_hit
      (Some (((((prefix, prefix_state), data), attacker_state),
        checked_result), checked_final_state))"
proof -
  have witness:
    "\<exists>result final_state trace_table composition_table as query_idxs dg
        composition_fri_roots final rest trace_tree composition_tree.
      Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))) \<and>
      accepted_with_bound_tables
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) trace_table composition_table as
        query_idxs \<and>
      verifier_header_transcript
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        as dg composition_fri_roots final rest \<and>
      created_tree trace_table trace_tree final_state \<and>
      created_tree composition_table composition_tree final_state \<and>
      hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
    using verify_out bound header trace_created composition_created tree_hit
    by blast
  show ?thesis
    unfolding
      checked_staged_security_with_actual_alpha_prefix_tree_output_hit_def
      Let_def
    using witness by simp
qed

definition checked_staged_security_with_data_state_alpha_prefix_tree_output_hit
  :: "'f staged_adversary \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_data_state_alpha_prefix_tree_output_hit A
      out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), _), _) \<Rightarrow>
          (let s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in \<exists>prefix prefix_state result final_state trace_table
              composition_table as query_idxs dg composition_fri_roots final
              rest trace_tree composition_tree.
            Some (prefix, prefix_state) \<in>
              set_dist
                (execute (staged_alpha_prefix_program A)
                  adversary_initial_state) \<and>
            staged_trace_root data = fst prefix \<and>
            staged_trace_fri_roots data = fst (snd prefix) \<and>
            staged_trace_fri_challenges data = fst (snd (snd prefix)) \<and>
            staged_trace_final data = snd (snd (snd prefix)) \<and>
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

lemma checked_staged_security_with_data_state_alpha_prefix_bad_set_hit_alphas_in_space:
  assumes hit:
    "checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
      bad_sets out"
  shows
    "case out of
      None \<Rightarrow> False
    | Some (((data, _), _), _) \<Rightarrow> staged_alphas data \<in> alpha_space"
  using hit
  unfolding checked_staged_security_with_data_state_alpha_prefix_bad_set_hit_def
    alpha_prefix_union_bad_sets_def
  by (auto split: option.splits prod.splits)

lemma checked_staged_security_with_data_state_alpha_prefix_bad_set_hit_bound_from_transcript:
  assumes transcript_bound:
    "wp_event (checked_staged_transcript_program A)
      (checked_staged_transcript_alpha_prefix_bad_set_hit A bad_sets)
      adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
        bad_sets)
      adversary_initial_state \<le> C"
  unfolding checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_head_event[OF transcript_bound])
  show
    "checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
      bad_sets None \<Longrightarrow>
     checked_staged_transcript_alpha_prefix_bad_set_hit A bad_sets None"
    unfolding
      checked_staged_security_with_data_state_alpha_prefix_bad_set_hit_def
      checked_staged_transcript_alpha_prefix_bad_set_hit_def
    by simp
next
  fix data attacker_state out
  assume cont:
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
      "checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
        bad_sets out"
  show
    "checked_staged_transcript_alpha_prefix_bad_set_hit A bad_sets
      (Some (data, attacker_state))"
  proof (cases out)
    case None
    then show ?thesis
      using hit
      unfolding
        checked_staged_security_with_data_state_alpha_prefix_bad_set_hit_def
      by simp
  next
    case (Some result_pack)
    then obtain data' attacker_state' result final_state where out_eq:
      "out = Some (((data', attacker_state'), result), final_state)"
      by (cases result_pack, auto split: prod.splits)
    have data_eq: "data' = data"
      and attacker_eq: "attacker_state' = attacker_state"
      using cont unfolding out_eq
      by (auto elim!: set_dist_bindE)
    show ?thesis
      using hit unfolding out_eq data_eq attacker_eq
        checked_staged_security_with_data_state_alpha_prefix_bad_set_hit_def
        checked_staged_transcript_alpha_prefix_bad_set_hit_def
      by simp
  qed
qed

lemma staged_after_alpha_prefix_program_outcome_extension:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (staged_after_alpha_prefix_program A prefix) s)"
  shows "s \<le> t"
proof -
  obtain fr trace_roots trace_bs trace_final where prefix_eq:
    "prefix = (fr, trace_roots, trace_bs, trace_final)"
    by (cases prefix) simp
  from outcome[unfolded prefix_eq]
  obtain as s1 dg s2 s3 s4 composition_roots composition_bs s5
      composition_final s6 s7 query_chunks where
    alpha_out:
      "Some (as, s1) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s)"
    and degree_out:
      "Some (dg, s2) \<in> set_dist (execute (degree_stage A as) s1)"
    and record_degree_out:
      "Some ((), s3) \<in> set_dist (execute (record_staged_message dg) s2)"
    and assert_out:
      "Some ((), s4) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))
            s3)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s5) \<in>
        set_dist
          (execute
            (staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])
            s4)"
    and composition_final_out:
      "Some (composition_final, s6) \<in>
        set_dist (execute (composition_final_stage A dg composition_bs) s5)"
    and record_composition_final_out:
      "Some ((), s7) \<in>
        set_dist (execute (record_staged_message composition_final) s6)"
    and query_out:
      "Some (query_chunks, t) \<in>
        set_dist (execute (staged_query_program A 0 rounds) s7)"
    unfolding staged_after_alpha_prefix_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have degree_controlled:
    "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_final_controlled:
    "controlled_ro_program (composition_final_budget budgets)
      (composition_final_stage A dg composition_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have ext_s_s1: "s \<le> s1"
    by (rule hash_target_program_outcome_extension
        [OF hash_target_program_staged_alpha_program alpha_out])
  have ext_s1_s2: "s1 \<le> s2"
    using controlled_ro_program_extension[OF degree_controlled] degree_out
    unfolding hash_extension_preserving_def by blast
  have s3_eq:
    "s3 = s2\<lparr>
      PState := concat (PState s2) dg,
      PTranscript := PTranscript s2 @ [dg]\<rparr>"
    by (rule record_staged_message_outcome[OF record_degree_out])
  have ext_s2_s3: "s2 \<le> s3"
    unfolding s3_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have s4_eq: "s4 = s3"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have ext_s3_s4: "s3 \<le> s4"
    unfolding s4_eq by (simp add: hash_ext_refl)
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_bound:
    "0 + ceil_log (to_nat dg + 1) \<le>
      length (composition_fri_budgets budgets)"
    using wf round_bound unfolding staged_budget_wellformed_def by simp
  have ext_s4_s5: "s4 \<le> s5"
    using staged_composition_fri_program_alignment
        [OF controlled composition_bound composition_out]
    by simp
  have ext_s5_s6: "s5 \<le> s6"
    using controlled_ro_program_extension[OF composition_final_controlled]
      composition_final_out
    unfolding hash_extension_preserving_def by blast
  have s7_eq:
    "s7 = s6\<lparr>
      PState := concat (PState s6) composition_final,
      PTranscript := PTranscript s6 @ [composition_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_composition_final_out])
  have ext_s6_s7: "s6 \<le> s7"
    unfolding s7_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have query_bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have ext_s7_t: "s7 \<le> t"
    by (rule hash_target_program_outcome_extension
        [OF hash_target_program_staged_query_program[OF controlled query_bound]
          query_out])
  show ?thesis
    by (rule hash_ext_trans[OF ext_s_s1])
      (rule hash_ext_trans[OF ext_s1_s2],
       rule hash_ext_trans[OF ext_s2_s3],
       rule hash_ext_trans[OF ext_s3_s4],
       rule hash_ext_trans[OF ext_s4_s5],
       rule hash_ext_trans[OF ext_s5_s6],
       rule hash_ext_trans[OF ext_s6_s7 ext_s7_t])
qed

lemma checked_staged_after_alpha_prefix_program_outcome_extension:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (checked_staged_after_alpha_prefix_program A prefix) s)"
  shows "s \<le> t"
proof -
  obtain fr trace_roots trace_bs trace_final where prefix_eq:
    "prefix = (fr, trace_roots, trace_bs, trace_final)"
    by (cases prefix) simp
  from outcome[unfolded prefix_eq]
  obtain as s1 dg s2 s3 s4 composition_roots composition_bs s5
      composition_final s6 s7 query_chunks where
    alpha_out:
      "Some (as, s1) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s)"
    and degree_out:
      "Some (dg, s2) \<in> set_dist (execute (degree_stage A as) s1)"
    and record_degree_out:
      "Some ((), s3) \<in> set_dist (execute (record_staged_message dg) s2)"
    and assert_out:
      "Some ((), s4) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))
            s3)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s5) \<in>
        set_dist
          (execute
            (staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])
            s4)"
    and composition_final_out:
      "Some (composition_final, s6) \<in>
        set_dist (execute (composition_final_stage A dg composition_bs) s5)"
    and record_composition_final_out:
      "Some ((), s7) \<in>
        set_dist (execute (record_staged_message composition_final) s6)"
    and query_out:
      "Some (query_chunks, t) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              0 rounds)
            s7)"
    unfolding checked_staged_after_alpha_prefix_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have degree_controlled:
    "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_final_controlled:
    "controlled_ro_program (composition_final_budget budgets)
      (composition_final_stage A dg composition_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have ext_s_s1: "s \<le> s1"
    by (rule hash_target_program_outcome_extension
        [OF hash_target_program_staged_alpha_program alpha_out])
  have ext_s1_s2: "s1 \<le> s2"
    using controlled_ro_program_extension[OF degree_controlled] degree_out
    unfolding hash_extension_preserving_def by blast
  have s3_eq:
    "s3 = s2\<lparr>
      PState := concat (PState s2) dg,
      PTranscript := PTranscript s2 @ [dg]\<rparr>"
    by (rule record_staged_message_outcome[OF record_degree_out])
  have ext_s2_s3: "s2 \<le> s3"
    unfolding s3_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have s4_eq: "s4 = s3"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have ext_s3_s4: "s3 \<le> s4"
    unfolding s4_eq by (simp add: hash_ext_refl)
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_bound:
    "0 + ceil_log (to_nat dg + 1) \<le>
      length (composition_fri_budgets budgets)"
    using wf round_bound unfolding staged_budget_wellformed_def by simp
  have ext_s4_s5: "s4 \<le> s5"
    using staged_composition_fri_program_alignment
        [OF controlled composition_bound composition_out]
    by simp
  have ext_s5_s6: "s5 \<le> s6"
    using controlled_ro_program_extension[OF composition_final_controlled]
      composition_final_out
    unfolding hash_extension_preserving_def by blast
  have s7_eq:
    "s7 = s6\<lparr>
      PState := concat (PState s6) composition_final,
      PTranscript := PTranscript s6 @ [composition_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_composition_final_out])
  have ext_s6_s7: "s6 \<le> s7"
    unfolding s7_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have query_bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_program:
    "hash_relation_program (\<lambda>_ _. False) 0
      (sum_list (take rounds (drop 0 (query_opening_budgets budgets))) +
        rounds)
      (checked_staged_query_program A trace_roots composition_roots 0
        rounds)"
    by (rule hash_relation_program_checked_staged_query_program
        [OF controlled query_bound])
      simp
  have ext_s7_t: "s7 \<le> t"
    using query_program query_out
    unfolding hash_relation_program_def hash_extension_preserving_def
    by blast
  show ?thesis
    by (rule hash_ext_trans[OF ext_s_s1])
      (rule hash_ext_trans[OF ext_s1_s2],
       rule hash_ext_trans[OF ext_s2_s3],
       rule hash_ext_trans[OF ext_s3_s4],
       rule hash_ext_trans[OF ext_s4_s5],
       rule hash_ext_trans[OF ext_s5_s6],
       rule hash_ext_trans[OF ext_s6_s7 ext_s7_t])
qed

lemma checked_staged_transcript_with_alpha_prefix_program_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
    "Some (((prefix, prefix_state), data), attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_with_alpha_prefix_program A)
          adversary_initial_state)"
  obtains
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A) adversary_initial_state)"
    "staged_trace_root data = fst prefix"
    "staged_trace_fri_roots data = fst (snd prefix)"
    "staged_trace_fri_challenges data = fst (snd (snd prefix))"
    "staged_trace_final data = snd (snd (snd prefix))"
    "prefix_state \<le> attacker_state"
proof -
  from outcome obtain after_out where prefix_out:
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A) adversary_initial_state)"
    and after_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_after_alpha_prefix_program A prefix)
          prefix_state)"
    unfolding checked_staged_transcript_with_alpha_prefix_program_def
    by (auto elim!: set_dist_bindE)
  have prefix_ext: "prefix_state \<le> attacker_state"
    by (rule checked_staged_after_alpha_prefix_program_outcome_extension
        [OF _ _ after_out])
      (fact wf, fact controlled)
  have root_eq:
    "staged_trace_root data = fst prefix"
    and trace_roots_eq:
    "staged_trace_fri_roots data = fst (snd prefix)"
    and trace_bs_eq:
    "staged_trace_fri_challenges data = fst (snd (snd prefix))"
    and trace_final_eq:
    "staged_trace_final data = snd (snd (snd prefix))"
  proof -
    obtain fr trace_roots trace_bs trace_final where prefix_eq:
      "prefix = (fr, trace_roots, trace_bs, trace_final)"
      by (cases prefix) simp
    from after_out[unfolded prefix_eq]
    obtain as s1 dg s2 s3 composition_roots composition_bs s4
        composition_final s5 s6 query_chunks where ret:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (return
              \<lparr>staged_trace_root = fr,
               staged_trace_fri_roots = trace_roots,
               staged_trace_fri_challenges = trace_bs,
               staged_trace_final = trace_final,
               staged_alphas = as,
               staged_degree = dg,
               staged_composition_fri_roots = composition_roots,
               staged_composition_fri_challenges = composition_bs,
               staged_composition_final = composition_final,
               staged_query_chunks = query_chunks\<rparr>)
            s6)"
      unfolding checked_staged_after_alpha_prefix_program_def Let_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    have data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
      using ret by simp
    show "staged_trace_root data = fst prefix"
      unfolding prefix_eq data_eq by simp
    show "staged_trace_fri_roots data = fst (snd prefix)"
      unfolding prefix_eq data_eq by simp
    show "staged_trace_fri_challenges data = fst (snd (snd prefix))"
      unfolding prefix_eq data_eq by simp
    show "staged_trace_final data = snd (snd (snd prefix))"
      unfolding prefix_eq data_eq by simp
  qed
  show ?thesis
    by (rule that[OF prefix_out root_eq trace_roots_eq trace_bs_eq
          trace_final_eq prefix_ext])
qed

lemma checked_staged_transcript_program_alpha_prefix_support:
  assumes outcome:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  obtains prefix prefix_state
  where
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A)
          adversary_initial_state)"
    "staged_trace_root data = fst prefix"
    "staged_trace_fri_roots data = fst (snd prefix)"
    "staged_trace_fri_challenges data = fst (snd (snd prefix))"
    "staged_trace_final data = snd (snd (snd prefix))"
proof -
  have staged_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (staged_transcript_program A) adversary_initial_state)"
    by (rule checked_staged_transcript_program_outcome_imp_staged_transcript_program
        [OF outcome])
  then obtain prefix prefix_state where prefix_out:
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A)
          adversary_initial_state)"
    and after_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (staged_after_alpha_prefix_program A prefix)
          prefix_state)"
    unfolding staged_transcript_program_alpha_prefix_decomp
    by (auto elim!: set_dist_bindE)
  have root_eq:
    "staged_trace_root data = fst prefix"
    and trace_roots_eq:
    "staged_trace_fri_roots data = fst (snd prefix)"
    and trace_bs_eq:
    "staged_trace_fri_challenges data = fst (snd (snd prefix))"
    and trace_final_eq:
    "staged_trace_final data = snd (snd (snd prefix))"
  proof -
    obtain fr trace_roots trace_bs trace_final where prefix_eq:
      "prefix = (fr, trace_roots, trace_bs, trace_final)"
      by (cases prefix) simp
    from after_out[unfolded prefix_eq]
    obtain as s1 dg s2 s3 composition_roots composition_bs s4
        composition_final s5 s6 query_chunks where ret:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (return
              \<lparr>staged_trace_root = fr,
               staged_trace_fri_roots = trace_roots,
               staged_trace_fri_challenges = trace_bs,
               staged_trace_final = trace_final,
               staged_alphas = as,
               staged_degree = dg,
               staged_composition_fri_roots = composition_roots,
               staged_composition_fri_challenges = composition_bs,
               staged_composition_final = composition_final,
               staged_query_chunks = query_chunks\<rparr>)
            s6)"
      unfolding staged_after_alpha_prefix_program_def Let_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    have data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
      using ret by simp
    show "staged_trace_root data = fst prefix"
      unfolding prefix_eq data_eq by simp
    show "staged_trace_fri_roots data = fst (snd prefix)"
      unfolding prefix_eq data_eq by simp
    show "staged_trace_fri_challenges data = fst (snd (snd prefix))"
      unfolding prefix_eq data_eq by simp_all
    show "staged_trace_final data = snd (snd (snd prefix))"
      unfolding prefix_eq data_eq by simp
  qed
  show ?thesis
    by (rule that[OF prefix_out root_eq trace_roots_eq trace_bs_eq
          trace_final_eq])
qed

lemma checked_staged_transcript_program_alpha_prefix_match_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  obtains prefix prefix_state
  where
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A)
          adversary_initial_state)"
    "staged_trace_root data = fst prefix"
    "staged_trace_fri_roots data = fst (snd prefix)"
    "staged_trace_fri_challenges data = fst (snd (snd prefix))"
    "staged_trace_final data = snd (snd (snd prefix))"
    "prefix_state \<le> attacker_state"
proof -
  have staged_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (staged_transcript_program A) adversary_initial_state)"
    by (rule checked_staged_transcript_program_outcome_imp_staged_transcript_program
        [OF outcome])
  then obtain prefix prefix_state where prefix_out:
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A)
          adversary_initial_state)"
    and after_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (staged_after_alpha_prefix_program A prefix)
          prefix_state)"
    unfolding staged_transcript_program_alpha_prefix_decomp
    by (auto elim!: set_dist_bindE)
  have prefix_ext: "prefix_state \<le> attacker_state"
    by (rule staged_after_alpha_prefix_program_outcome_extension
        [OF wf controlled after_out])
  have root_eq:
    "staged_trace_root data = fst prefix"
    and trace_roots_eq:
    "staged_trace_fri_roots data = fst (snd prefix)"
    and trace_bs_eq:
    "staged_trace_fri_challenges data = fst (snd (snd prefix))"
    and trace_final_eq:
    "staged_trace_final data = snd (snd (snd prefix))"
  proof -
    obtain fr trace_roots trace_bs trace_final where prefix_eq:
      "prefix = (fr, trace_roots, trace_bs, trace_final)"
      by (cases prefix) simp
    from after_out[unfolded prefix_eq]
    obtain as s1 dg s2 s3 composition_roots composition_bs s4
        composition_final s5 s6 query_chunks where ret:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (return
              \<lparr>staged_trace_root = fr,
               staged_trace_fri_roots = trace_roots,
               staged_trace_fri_challenges = trace_bs,
               staged_trace_final = trace_final,
               staged_alphas = as,
               staged_degree = dg,
               staged_composition_fri_roots = composition_roots,
               staged_composition_fri_challenges = composition_bs,
               staged_composition_final = composition_final,
               staged_query_chunks = query_chunks\<rparr>)
            s6)"
      unfolding staged_after_alpha_prefix_program_def Let_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    have data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
      using ret by simp
    show "staged_trace_root data = fst prefix"
      unfolding prefix_eq data_eq by simp
    show "staged_trace_fri_roots data = fst (snd prefix)"
      unfolding prefix_eq data_eq by simp
    show "staged_trace_fri_challenges data = fst (snd (snd prefix))"
      unfolding prefix_eq data_eq by simp
    show "staged_trace_final data = snd (snd (snd prefix))"
      unfolding prefix_eq data_eq by simp
  qed
  show ?thesis
    by (rule that[OF prefix_out root_eq trace_roots_eq trace_bs_eq
          trace_final_eq prefix_ext])
qed

lemma checked_staged_security_with_data_state_alpha_prefix_tree_output_hitI:
  assumes prefix_out:
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
    and verify_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
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
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        as dg composition_fri_roots final rest"
    and trace_created: "created_tree trace_table trace_tree final_state"
    and composition_created:
      "created_tree composition_table composition_tree final_state"
    and tree_hit:
      "hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
  shows
    "checked_staged_security_with_data_state_alpha_prefix_tree_output_hit A
      (Some (((data, attacker_state), checked_result), checked_final_state))"
proof -
  have prefix_tuple:
    "prefix =
      (staged_trace_root data, staged_trace_fri_roots data,
       staged_trace_fri_challenges data, staged_trace_final data)"
    by (cases prefix; cases "snd prefix"; cases "snd (snd prefix)")
      (use root_eq trace_roots_eq trace_bs_eq trace_final_eq in auto)
  show ?thesis
    unfolding checked_staged_security_with_data_state_alpha_prefix_tree_output_hit_def
      Let_def
    apply (simp add: prefix_tuple)
    apply (rule exI[where x=prefix_state])
    apply (rule conjI)
     using prefix_out prefix_tuple
     apply simp
    apply (rule exI[where x=result])
    apply (rule exI[where x=final_state])
    apply (rule conjI)
     using verify_out
     apply simp
    apply (rule exI[where x=trace_table])
    apply (rule exI[where x=composition_table])
    apply (rule exI[where x=as])
    apply (rule conjI)
     apply (rule exI[where x=query_idxs])
     using bound
     apply simp
    apply (rule conjI)
    apply (rule exI[where x=dg])
    apply (rule exI[where x=composition_fri_roots])
    apply (rule exI[where x=final])
    apply (rule exI[where x=rest])
     using header
     apply simp
    apply (rule exI[where x=trace_tree])
    apply (rule conjI)
     using trace_created
     apply simp
    apply (rule exI[where x=composition_tree])
    using composition_created tree_hit
    apply simp
    done
qed

lemma checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit_imp_prefix_or_tree_output_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
        bad_sets out"
  shows
    "checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
        bad_sets out \<or>
      checked_staged_security_with_data_state_alpha_prefix_tree_output_hit A
        out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit_def
    by simp
next
  case (Some result_pack)
  then obtain data attacker_state checked_result checked_final_state where
    out_eq:
      "out =
        Some (((data, attacker_state), checked_result),
          checked_final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have support_some:
    "Some (((data, attacker_state), checked_result),
        checked_final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    using support unfolding out_eq .
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support_some]
  have builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and checked_verify:
      "Some (checked_result, checked_final_state) \<in>
        set_dist (execute verify_monad ?s)"
    by blast+
  from checked_staged_transcript_program_alpha_prefix_match_support
      [OF wf controlled builder]
  obtain prefix prefix_state where prefix_out:
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
    by blast
  have prefix_tuple:
    "prefix =
      (staged_trace_root data, staged_trace_fri_roots data,
       staged_trace_fri_challenges data, staged_trace_final data)"
    by (cases prefix; cases "snd prefix"; cases "snd (snd prefix)")
      (use root_eq trace_roots_eq trace_bs_eq trace_final_eq in auto)
  have union_bad:
    "staged_alphas data \<in>
      alpha_header_supported_union_bad_sets ?s bad_sets
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)"
    using hit unfolding out_eq
      checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit_def
    by simp
  then have alphas_space: "staged_alphas data \<in> alpha_space"
    unfolding alpha_header_supported_union_bad_sets_def by auto
  from union_bad obtain trace_table where header_candidate:
      "trace_table \<in>
        alpha_header_supported_trace_table_candidates ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)"
    and bad:
      "staged_alphas data \<in> bad_sets trace_table"
    unfolding alpha_header_supported_union_bad_sets_def by blast
  from header_candidate obtain candidate_out composition_table as query_idxs
      dg composition_fri_roots final rest where candidate_out:
      "candidate_out \<in> set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s candidate_out trace_table
        composition_table as query_idxs"
    and candidate_header:
      "verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        as dg composition_fri_roots final rest"
    unfolding alpha_header_supported_trace_table_candidates_def by blast
  from bound obtain result final_state where candidate_out_eq:
      "candidate_out = Some (result, final_state)"
    unfolding accepted_with_bound_tables_def by blast
  have verifier_out:
    "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    using candidate_out candidate_out_eq by simp
  have bound_some:
    "accepted_with_bound_tables ?s (Some (result, final_state))
      trace_table composition_table as query_idxs"
    using bound candidate_out_eq by simp
  have prefix_s: "prefix_state \<le> ?s"
    by (rule
        alpha_prefix_hash_extends_verifier_state_from_adversary_right
        [OF prefix_ext])
  have s_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier_out])
  have prefix_final: "prefix_state \<le> final_state"
    by (rule hash_ext_trans[OF prefix_s s_final])
  show ?thesis
  proof (rule
      accepted_with_bound_tables_initial_roots_pullback_or_new_tree_output_hit
        [OF prefix_final bound_some])
    fix fr f_fri_roots f_final dg' composition_fri_roots' final'
      rest' trace_tree composition_tree
    assume pull_header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg'
        composition_fri_roots' final' rest'"
      and trace_created:
        "created_tree trace_table trace_tree final_state"
      and composition_created:
        "created_tree composition_table composition_tree final_state"
      and split:
        "(merkle_root_binds_table fr trace_table prefix_state \<and>
          merkle_root_binds_table (hd composition_fri_roots')
            composition_table prefix_state) \<or>
          hash_map_new_output_hit
            (set_tree trace_tree \<union> set_tree composition_tree)
            prefix_state final_state"
    have pull_header_eq:
      "fr = staged_trace_root data \<and>
       f_fri_roots = staged_trace_fri_roots data \<and>
       f_final = staged_trace_final data \<and>
       dg' = dg \<and>
       composition_fri_roots' = composition_fri_roots \<and>
       final' = final \<and>
       rest' = rest"
      using verifier_header_transcript_unique[OF candidate_header pull_header]
      by simp
    then have fr_eq: "fr = staged_trace_root data"
      by simp
    from split show ?thesis
    proof
      assume binds:
        "merkle_root_binds_table fr trace_table prefix_state \<and>
         merkle_root_binds_table (hd composition_fri_roots')
          composition_table prefix_state"
      have trace_len: "length trace_table = clength * scale"
        using bound_some unfolding accepted_with_bound_tables_def
          accepted_with_tables_def by simp
      have prefix_candidate:
        "trace_table \<in>
          alpha_prefix_trace_table_candidates prefix_state
            (staged_trace_root data)"
        by (rule alpha_prefix_trace_table_candidateI[OF trace_len])
          (use binds fr_eq in simp)
      have prefix_bad:
        "staged_alphas data \<in>
          alpha_prefix_union_bad_sets prefix_state bad_sets
            (staged_trace_root data)"
        unfolding alpha_prefix_union_bad_sets_def
        using alphas_space prefix_candidate bad by auto
      have
        "checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
          bad_sets out"
        unfolding out_eq
          checked_staged_security_with_data_state_alpha_prefix_bad_set_hit_def
        apply simp
        apply (rule exI[where x=prefix_state])
        using prefix_out prefix_tuple prefix_bad
        apply simp
        done
      then show ?thesis by simp
    next
      assume tree_hit:
        "hash_map_new_output_hit
          (set_tree trace_tree \<union> set_tree composition_tree)
          prefix_state final_state"
      have
        "checked_staged_security_with_data_state_alpha_prefix_tree_output_hit A
          out"
        unfolding out_eq
        by (rule
            checked_staged_security_with_data_state_alpha_prefix_tree_output_hitI
            [OF prefix_out root_eq trace_roots_eq trace_bs_eq trace_final_eq
              verifier_out bound_some candidate_header trace_created
              composition_created tree_hit])
      then show ?thesis by simp
    qed
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_header_supported_bad_set_hit_imp_prefix_or_tree_output_hit_on_support:
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
      "checked_staged_security_with_actual_alpha_prefix_header_supported_bad_set_hit
        bad_sets out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        bad_sets out \<or>
      checked_staged_security_with_actual_alpha_prefix_tree_output_hit out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_actual_alpha_prefix_header_supported_bad_set_hit_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state checked_result
      checked_final_state where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state),
          checked_result), checked_final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have support_some:
    "Some (((((prefix, prefix_state), data), attacker_state),
        checked_result), checked_final_state) \<in>
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
    and checked_verify:
      "Some (checked_result, checked_final_state) \<in>
        set_dist (execute verify_monad ?s)"
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
  have union_bad:
    "staged_alphas data \<in>
      alpha_header_supported_union_bad_sets ?s bad_sets
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)"
    using hit unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_header_supported_bad_set_hit_def
      Let_def
    by simp
  then have alphas_space: "staged_alphas data \<in> alpha_space"
    unfolding alpha_header_supported_union_bad_sets_def by auto
  from union_bad obtain trace_table where header_candidate:
      "trace_table \<in>
        alpha_header_supported_trace_table_candidates ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)"
    and bad:
      "staged_alphas data \<in> bad_sets trace_table"
    unfolding alpha_header_supported_union_bad_sets_def by blast
  from header_candidate obtain candidate_out composition_table as query_idxs
      dg composition_fri_roots final rest where candidate_out:
      "candidate_out \<in> set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s candidate_out trace_table
        composition_table as query_idxs"
    and candidate_header:
      "verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        as dg composition_fri_roots final rest"
    unfolding alpha_header_supported_trace_table_candidates_def by blast
  from bound obtain result final_state where candidate_out_eq:
      "candidate_out = Some (result, final_state)"
    unfolding accepted_with_bound_tables_def by blast
  have verifier_out:
    "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    using candidate_out candidate_out_eq by simp
  have bound_some:
    "accepted_with_bound_tables ?s (Some (result, final_state))
      trace_table composition_table as query_idxs"
    using bound candidate_out_eq by simp
  have prefix_s: "prefix_state \<le> ?s"
    by (rule
        alpha_prefix_hash_extends_verifier_state_from_adversary_right
        [OF prefix_ext])
  have s_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier_out])
  have prefix_final: "prefix_state \<le> final_state"
    by (rule hash_ext_trans[OF prefix_s s_final])
  show ?thesis
  proof (rule
      accepted_with_bound_tables_initial_roots_pullback_or_new_tree_output_hit
        [OF prefix_final bound_some])
    fix fr f_fri_roots f_final dg' composition_fri_roots' final'
      rest' trace_tree composition_tree
    assume pull_header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg'
        composition_fri_roots' final' rest'"
      and trace_created:
      "created_tree trace_table trace_tree final_state"
      and composition_created:
      "created_tree composition_table composition_tree final_state"
      and split:
      "(merkle_root_binds_table fr trace_table prefix_state \<and>
        merkle_root_binds_table (hd composition_fri_roots')
          composition_table prefix_state) \<or>
        hash_map_new_output_hit
          (set_tree trace_tree \<union> set_tree composition_tree)
          prefix_state final_state"
    have pull_header_eq:
      "fr = staged_trace_root data \<and>
       f_fri_roots = staged_trace_fri_roots data \<and>
       f_final = staged_trace_final data \<and>
       dg' = dg \<and>
       composition_fri_roots' = composition_fri_roots \<and>
       final' = final \<and>
       rest' = rest"
      using verifier_header_transcript_unique[OF candidate_header pull_header]
      by simp
    then have fr_eq: "fr = staged_trace_root data"
      by simp
    from split show ?thesis
    proof
      assume binds:
        "merkle_root_binds_table fr trace_table prefix_state \<and>
         merkle_root_binds_table (hd composition_fri_roots')
          composition_table prefix_state"
      have trace_len: "length trace_table = clength * scale"
        using bound_some unfolding accepted_with_bound_tables_def
          accepted_with_tables_def by simp
      have prefix_candidate:
        "trace_table \<in>
          alpha_prefix_trace_table_candidates prefix_state (fst prefix)"
        by (rule alpha_prefix_trace_table_candidateI[OF trace_len])
          (use binds fr_eq root_eq in simp)
      have prefix_bad:
        "staged_alphas data \<in>
          alpha_prefix_union_bad_sets prefix_state bad_sets (fst prefix)"
        unfolding alpha_prefix_union_bad_sets_def
        using alphas_space prefix_candidate bad by auto
      have
        "checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          bad_sets out"
        unfolding out_eq
          checked_staged_security_with_actual_alpha_prefix_bad_set_hit_def
          Let_def
        using prefix_bad
        by simp
      then show ?thesis by simp
    next
      assume tree_hit:
        "hash_map_new_output_hit
          (set_tree trace_tree \<union> set_tree composition_tree)
          prefix_state final_state"
      have
        "checked_staged_security_with_actual_alpha_prefix_tree_output_hit
          out"
        unfolding out_eq
        by (rule
            checked_staged_security_with_actual_alpha_prefix_tree_output_hitI
            [OF verifier_out bound_some candidate_header trace_created
              composition_created tree_hit])
      then show ?thesis by simp
    qed
  qed
qed

lemma checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit_bound_from_actual_prefix_and_tree:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          bad_sets)
        adversary_initial_state \<le> P"
    and tree_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_tree_output_hit
        adversary_initial_state \<le> T"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
        bad_sets)
      adversary_initial_state \<le> P + T"
proof -
  let ?M =
    "checked_staged_security_experiment_with_actual_alpha_prefix_data_state A"
  let ?Prefix =
    "checked_staged_security_with_actual_alpha_prefix_bad_set_hit bad_sets"
  let ?Tree = "checked_staged_security_with_actual_alpha_prefix_tree_output_hit"
  let ?Header =
    "checked_staged_security_with_actual_alpha_prefix_header_supported_bad_set_hit
      bad_sets"
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
        bad_sets)
      adversary_initial_state =
    wp_event ?M ?Header adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit_actual_projection)
  also have "... \<le> wp_event ?M (\<lambda>out. ?Prefix out \<or> ?Tree out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit: "?Header out"
    show "?Prefix out \<or> ?Tree out"
      by (rule
          checked_staged_security_with_actual_alpha_prefix_header_supported_bad_set_hit_imp_prefix_or_tree_output_hit_on_support
          [OF wf controlled support hit])
  qed
  also have "... \<le>
      wp_event ?M ?Prefix adversary_initial_state +
      wp_event ?M ?Tree adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> P + T"
    by (rule add_mono[OF prefix_bound tree_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit_bound_from_prefix_and_tree:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
          bad_sets)
        adversary_initial_state \<le> P"
    and tree_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_prefix_tree_output_hit A)
        adversary_initial_state \<le> T"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
        bad_sets)
      adversary_initial_state \<le> P + T"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?Prefix =
    "checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
      bad_sets"
  let ?Tree =
    "checked_staged_security_with_data_state_alpha_prefix_tree_output_hit A"
  let ?Header =
    "checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
      bad_sets"
  have "wp_event ?M ?Header adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?Prefix out \<or> ?Tree out)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit: "?Header out"
    show "?Prefix out \<or> ?Tree out"
      by (rule
          checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit_imp_prefix_or_tree_output_hit_on_support
          [OF wf controlled support hit])
  qed
  also have "... \<le>
      wp_event ?M ?Prefix adversary_initial_state +
      wp_event ?M ?Tree adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> P + T"
    by (rule add_mono[OF prefix_bound tree_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_alpha_prefix_and_tree:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and tree_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_prefix_tree_output_hit A)
        adversary_initial_state \<le> T"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le> P + T"
proof -
  have alpha_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> P + T"
    by (rule
        checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit_bound_from_prefix_and_tree
        [OF wf controlled prefix_bound tree_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_alpha_header_supported_bad_set_general
        [OF wf controlled alpha_bound])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_actual_alpha_prefix_and_tree:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and tree_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_tree_output_hit
        adversary_initial_state \<le> T"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le> P + T"
proof -
  have alpha_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> P + T"
    by (rule
        checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit_bound_from_actual_prefix_and_tree
        [OF wf controlled prefix_bound tree_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_alpha_header_supported_bad_set_general
        [OF wf controlled alpha_bound])
qed

end

end
