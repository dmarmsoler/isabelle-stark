(*  Title:      Stark/Soundness_FRI_Zero_Round_Query_List_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Zero_Round_Query_List_Bounds
  imports
    Soundness_FRI_Zero_Round_Target
    Soundness_FRI_Query_List_Exact_Product
begin

text \<open>
  Exact staged query-list bounds for fixed zero-round FRI targets.

  The target table and final value must already be fixed before query
  sampling.  This theory deliberately does not close the remaining
  candidate/verifier alignment gap; it only packages the exact-product query
  accounting for the fixed targets isolated in
  @{text Soundness_FRI_Zero_Round_Target}.
\<close>

context soundness
begin

definition fri_zero_round_first_query_index_lists
  :: "'f list \<Rightarrow> 'f \<Rightarrow> nat list set"
where
  "fri_zero_round_first_query_index_lists table final =
    {query_idxs \<in> fri_query_index_list_space.
      query_idxs ! 0 \<in> fri_final_value_agreement_set table final}"

lemma fri_zero_round_first_query_index_lists_subset:
  "fri_zero_round_first_query_index_lists table final
    \<subseteq> fri_query_index_list_space"
  unfolding fri_zero_round_first_query_index_lists_def by blast

lemma finite_fri_zero_round_first_query_index_lists[simp]:
  "finite (fri_zero_round_first_query_index_lists table final)"
  by (rule finite_subset
      [OF fri_zero_round_first_query_index_lists_subset])
    (rule finite_fri_query_index_list_space)

lemma fri_zero_round_first_query_index_listsD:
  assumes "query_idxs \<in>
    fri_zero_round_first_query_index_lists table final"
  shows "query_idxs \<in> fri_query_index_list_space"
    and "query_idxs ! 0 \<in> fri_final_value_agreement_set table final"
  using assms
  unfolding fri_zero_round_first_query_index_lists_def by blast+

lemma fri_zero_round_first_query_index_lists_card_le:
  "card (fri_zero_round_first_query_index_lists table final) \<le>
    card (fri_final_value_agreement_set table final) *
      card query_sample_space ^ (rounds - 1)"
proof -
  let ?T = "fri_zero_round_first_query_index_lists table final"
  let ?Tail =
    "{xs. set xs \<subseteq> query_sample_space \<and>
      length xs = rounds - 1}"
  let ?F = "\<lambda>query_idxs. (query_idxs ! 0, tl query_idxs)"
  have image_subset:
    "?F ` ?T \<subseteq>
      fri_final_value_agreement_set table final \<times> ?Tail"
  proof
    fix y
    assume "y \<in> ?F ` ?T"
    then obtain query_idxs where query_idxs_in: "query_idxs \<in> ?T"
      and y_def: "y = ?F query_idxs"
      by blast
    have query_space: "query_idxs \<in> fri_query_index_list_space"
      and first_in:
        "query_idxs ! 0 \<in> fri_final_value_agreement_set table final"
      using fri_zero_round_first_query_index_listsD[OF query_idxs_in]
      by blast+
    have len: "length query_idxs = rounds"
      and set_subset: "set query_idxs \<subseteq> query_sample_space"
      using query_space unfolding fri_query_index_list_space_def by auto
    have tail_len: "length (tl query_idxs) = rounds - 1"
      using len rounds_positive by (cases query_idxs) simp_all
    have tail_set: "set (tl query_idxs) \<subseteq> set query_idxs"
      by (cases query_idxs) auto
    have tail_subset: "set (tl query_idxs) \<subseteq> query_sample_space"
      using tail_set set_subset by blast
    show "y \<in> fri_final_value_agreement_set table final \<times> ?Tail"
      using y_def first_in tail_len tail_subset by simp
  qed
  have inj: "inj_on ?F ?T"
  proof (rule inj_onI)
    fix xs ys
    assume xs_in: "xs \<in> ?T"
      and ys_in: "ys \<in> ?T"
      and eq: "?F xs = ?F ys"
    have xs_len: "length xs = rounds"
      and ys_len: "length ys = rounds"
      using fri_zero_round_first_query_index_listsD(1)[OF xs_in]
        fri_zero_round_first_query_index_listsD(1)[OF ys_in]
      unfolding fri_query_index_list_space_def by auto
    have xs_ne: "xs \<noteq> []"
      and ys_ne: "ys \<noteq> []"
      using xs_len ys_len rounds_positive by auto
    have head_eq: "xs ! 0 = ys ! 0"
      using eq by simp
    have tail_eq: "tl xs = tl ys"
      using eq by simp
    from xs_ne obtain x xs' where xs_def: "xs = x # xs'"
      by (cases xs) auto
    from ys_ne obtain y ys' where ys_def: "ys = y # ys'"
      by (cases ys) auto
    show "xs = ys"
      using head_eq tail_eq unfolding xs_def ys_def by simp
  qed
  have "card ?T = card (?F ` ?T)"
    using inj by (rule card_image[symmetric])
  also have "... \<le>
      card (fri_final_value_agreement_set table final \<times> ?Tail)"
  proof (rule card_mono)
    show "finite (fri_final_value_agreement_set table final \<times> ?Tail)"
      by (intro finite_cartesian_product finite_fri_final_value_agreement_set
          finite_lists_length_eq[OF finite_query_sample_space])
    show "?F ` ?T \<subseteq> fri_final_value_agreement_set table final \<times> ?Tail"
      by (rule image_subset)
  qed
  also have "... =
      card (fri_final_value_agreement_set table final) * card ?Tail"
    by (simp add: card_cartesian_product)
  also have "card ?Tail = card query_sample_space ^ (rounds - 1)"
    by (rule card_lists_length_eq[OF finite_query_sample_space])
  finally show ?thesis .
qed

lemma fri_zero_round_first_query_index_lists_card_bound_from_small:
  assumes small:
    "card (fri_final_value_agreement_set table final) <
      query_sample_space_size"
  shows "card (fri_zero_round_first_query_index_lists table final) \<le>
    (query_sample_space_size - 1) *
      query_sample_space_size ^ (rounds - 1)"
proof -
  have agreement_le:
    "card (fri_final_value_agreement_set table final) \<le>
      query_sample_space_size - 1"
    using small by linarith
  have "card (fri_zero_round_first_query_index_lists table final) \<le>
      card (fri_final_value_agreement_set table final) *
        card query_sample_space ^ (rounds - 1)"
    by (rule fri_zero_round_first_query_index_lists_card_le)
  also have "... \<le>
      (query_sample_space_size - 1) *
        query_sample_space_size ^ (rounds - 1)"
    using agreement_le by simp
  finally show ?thesis .
qed

definition trace_fri_zero_round_query_list_target_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_zero_round_query_list_target_hit s out \<longleftrightarrow>
    (\<exists>trace_table trace_final.
      trace_fri_query_index_list_set_hit s
        (fri_zero_round_first_query_index_lists trace_table trace_final)
        out \<and>
      card (fri_final_value_agreement_set trace_table trace_final) <
        query_sample_space_size)"

lemma trace_fri_zero_round_query_list_target_hitE:
  assumes "trace_fri_zero_round_query_list_target_hit s out"
  obtains trace_table trace_final where
    "trace_fri_query_index_list_set_hit s
      (fri_zero_round_first_query_index_lists trace_table trace_final)
      out"
    "card (fri_final_value_agreement_set trace_table trace_final) <
      query_sample_space_size"
  using assms
  unfolding trace_fri_zero_round_query_list_target_hit_def by blast

lemma trace_fri_zero_round_checked_first_query_target_hit_imp_query_list_target:
  assumes "trace_fri_zero_round_checked_first_query_target_hit s out"
  shows "trace_fri_zero_round_query_list_target_hit s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
      and first_hit:
        "fri_query_idxs ! 0 \<in>
          fri_final_value_agreement_set trace_table trace_final"
      and card_lt:
        "card (fri_final_value_agreement_set trace_table trace_final) <
          query_sample_space_size"
    unfolding trace_fri_zero_round_checked_first_query_target_hit_def
    by blast
  have query_space:
    "fri_query_idxs \<in> fri_query_index_list_space"
    by (rule accepted_fri_opening_transcript_query_index_list_space
        [OF fri_openings])
  have query_target:
    "fri_query_idxs \<in>
      fri_zero_round_first_query_index_lists trace_table trace_final"
    using query_space first_hit
    unfolding fri_zero_round_first_query_index_lists_def by simp
  have hit:
    "trace_fri_query_index_list_set_hit s
      (fri_zero_round_first_query_index_lists trace_table trace_final) out"
    unfolding trace_fri_query_index_list_set_hit_def
    using fri_openings query_target by blast
  show ?thesis
    unfolding trace_fri_zero_round_query_list_target_hit_def
    using hit card_lt by blast
qed

lemma trace_fri_zero_round_candidate_first_query_target_hit_imp_query_list_target_or_alignment_gap:
  assumes "trace_fri_zero_round_candidate_first_query_target_hit s out"
  shows
    "trace_fri_zero_round_query_list_target_hit s out \<or>
     trace_fri_zero_round_candidate_first_query_alignment_gap s out"
proof (rule trace_fri_zero_round_candidate_first_query_target_hitE[OF assms])
  fix trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
  assume evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    and rounds_empty: "length trace_bs = 0"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
    and candidate_first_hit:
      "candidate_query_idxs ! 0 \<in>
        fri_final_value_agreement_set trace_table trace_final"
    and card_lt:
      "card (fri_final_value_agreement_set trace_table trace_final) <
        query_sample_space_size"
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    by (rule trace_fri_partial_candidate_opening_evidenceD(1)
        [OF evidence])
  show ?thesis
  proof (cases "fri_query_idxs ! 0 \<in>
      fri_final_value_agreement_set trace_table trace_final")
    case True
    have query_space:
      "fri_query_idxs \<in> fri_query_index_list_space"
      by (rule accepted_fri_opening_transcript_query_index_list_space
          [OF fri_openings])
    have query_target:
      "fri_query_idxs \<in>
        fri_zero_round_first_query_index_lists trace_table trace_final"
      using query_space True
      unfolding fri_zero_round_first_query_index_lists_def by simp
    have hit:
      "trace_fri_query_index_list_set_hit s
        (fri_zero_round_first_query_index_lists trace_table trace_final)
        out"
      unfolding trace_fri_query_index_list_set_hit_def
      using fri_openings query_target by blast
    have "trace_fri_zero_round_query_list_target_hit s out"
      unfolding trace_fri_zero_round_query_list_target_hit_def
      using hit card_lt by blast
    then show ?thesis by blast
  next
    case False
    have gap:
      "trace_fri_zero_round_candidate_first_query_alignment_gap s out"
      unfolding trace_fri_zero_round_candidate_first_query_alignment_gap_def
      by (intro exI conjI)
        (rule evidence, rule rounds_empty, rule not_final,
         rule candidate_first_hit, rule False, rule card_lt)
    then show ?thesis by blast
  qed
qed

lemma trace_fri_zero_round_final_obstruction_imp_query_list_target_or_candidate_gaps:
  assumes "trace_fri_zero_round_final_obstruction s out"
  shows
    "trace_fri_zero_round_query_list_target_hit s out \<or>
     trace_fri_zero_round_candidate_first_query_value_gap s out \<or>
     trace_fri_zero_round_candidate_first_query_alignment_gap s out"
proof (rule trace_fri_zero_round_final_obstruction_agreement_set_card_lt
    [OF assms])
  fix trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
  assume evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    and rounds_empty: "length trace_bs = 0"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
    and card_lt:
      "card (fri_final_value_agreement_set trace_table trace_final) <
        query_sample_space_size"
  show ?thesis
  proof (cases "candidate_query_idxs ! 0 \<in>
      fri_final_value_agreement_set trace_table trace_final")
    case True
    have candidate_hit:
      "trace_fri_zero_round_candidate_first_query_target_hit s out"
      unfolding trace_fri_zero_round_candidate_first_query_target_hit_def
      by (intro exI conjI)
        (rule evidence, rule rounds_empty, rule not_final, rule True,
         rule card_lt)
    then show ?thesis
      using
        trace_fri_zero_round_candidate_first_query_target_hit_imp_query_list_target_or_alignment_gap
      by blast
  next
    case False
    have value_gap:
      "trace_fri_zero_round_candidate_first_query_value_gap s out"
      unfolding trace_fri_zero_round_candidate_first_query_value_gap_def
      by (intro exI conjI)
        (rule evidence, rule rounds_empty, rule not_final, rule False,
         rule card_lt)
    then show ?thesis by blast
  qed
qed

lemma wp_trace_fri_zero_round_final_obstruction_bound_from_query_list_target_and_candidate_gaps:
  assumes target_bound:
      "wp_event verify_monad
        (trace_fri_zero_round_query_list_target_hit s) s \<le> Q"
    and value_bound:
      "wp_event verify_monad
        (trace_fri_zero_round_candidate_first_query_value_gap s) s \<le> V"
    and alignment_bound:
      "wp_event verify_monad
        (trace_fri_zero_round_candidate_first_query_alignment_gap s) s \<le> A"
  shows
    "wp_event verify_monad
      (trace_fri_zero_round_final_obstruction s) s \<le> Q + V + A"
proof -
  have event_le:
    "wp_event verify_monad
      (trace_fri_zero_round_final_obstruction s) s \<le>
     wp_event verify_monad
      (\<lambda>out.
        trace_fri_zero_round_query_list_target_hit s out \<or>
        trace_fri_zero_round_candidate_first_query_value_gap s out \<or>
        trace_fri_zero_round_candidate_first_query_alignment_gap s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_zero_round_final_obstruction_imp_query_list_target_or_candidate_gaps)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_zero_round_query_list_target_hit s) s +
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_zero_round_candidate_first_query_value_gap s out \<or>
          trace_fri_zero_round_candidate_first_query_alignment_gap s out) s"
    by (rule wp_event_union_bound)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_zero_round_query_list_target_hit s) s +
      (wp_event verify_monad
        (trace_fri_zero_round_candidate_first_query_value_gap s) s +
       wp_event verify_monad
        (trace_fri_zero_round_candidate_first_query_alignment_gap s) s)"
    by (intro add_mono order.refl wp_event_union_bound)
  also have "... \<le> Q + (V + A)"
    by (intro add_mono target_bound value_bound alignment_bound)
  also have "... = Q + V + A"
    by (simp add: add.assoc)
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_zero_round_query_list_target_exact_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          trace_fri_query_index_list_set_hit s
            (fri_zero_round_first_query_index_lists table final)))
      adversary_initial_state \<le>
      nnreal
        (card (fri_zero_round_first_query_index_lists table final)) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (fri_zero_round_first_query_index_lists table final))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule checked_staged_security_trace_fri_query_index_list_set_hit_exact_product_bound
      [OF wf controlled fri_zero_round_first_query_index_lists_subset])

lemma checked_staged_security_trace_fri_zero_round_query_list_target_small_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and small:
      "card (fri_final_value_agreement_set table final) <
        query_sample_space_size"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          trace_fri_query_index_list_set_hit s
            (fri_zero_round_first_query_index_lists table final)))
      adversary_initial_state \<le>
      nnreal
        ((query_sample_space_size - 1) *
          query_sample_space_size ^ (rounds - 1)) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (fri_zero_round_first_query_index_lists table final))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  have exact:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          trace_fri_query_index_list_set_hit s
            (fri_zero_round_first_query_index_lists table final)))
      adversary_initial_state \<le>
      nnreal
        (card (fri_zero_round_first_query_index_lists table final)) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (fri_zero_round_first_query_index_lists table final))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_zero_round_query_list_target_exact_bound
        [OF wf controlled])
  have card_le:
    "card (fri_zero_round_first_query_index_lists table final) \<le>
      (query_sample_space_size - 1) *
        query_sample_space_size ^ (rounds - 1)"
    by (rule fri_zero_round_first_query_index_lists_card_bound_from_small
        [OF small])
  have product_le:
    "nnreal
        (card (fri_zero_round_first_query_index_lists table final)) *
        (1 / nnreal (card query_sample_space)) ^ rounds \<le>
      nnreal
        ((query_sample_space_size - 1) *
          query_sample_space_size ^ (rounds - 1)) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
  proof -
    have card_nn:
      "nnreal (card (fri_zero_round_first_query_index_lists table final)) \<le>
        nnreal
          ((query_sample_space_size - 1) *
            query_sample_space_size ^ (rounds - 1))"
      using of_nat_mono[OF card_le, where 'a = nnreal] by simp
    show ?thesis
      by (rule mult_right_mono[OF card_nn]) simp
  qed
  show ?thesis
    by (rule order_trans[OF exact add_mono[OF product_le order_refl]])
qed

end

end
