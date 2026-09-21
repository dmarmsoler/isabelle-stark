theory Soundness_FRI_Conditioned_Conceptual_Split
  imports
    Soundness_FRI_Conditioned_Multiround
begin

context soundness
begin

lemma conceptual_sampled_chain_conditioned_split:
  assumes challenge_space:
      "challenges \<in> fri_challenge_space n"
    and challenges_len: "length challenges = n"
    and round_count: "n = ceil_log (Suc d)"
    and eval_power: "clength * scale = 2 ^ N"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and layer_cover:
      "\<And>j. j \<le> n \<Longrightarrow>
        length (fri_canonical_domain_at j) \<le> length (layers ! j)"
    and committed_path:
      "\<And>j. j < n \<Longrightarrow>
        committed j (take j challenges) = layers ! j"
    and start_not_low:
      "\<not> fri_table_low_degree_on (fri_padded_degree_bound d)
        (fri_canonical_domain_at 0)
        (fri_conditioned_layer_table 0 (layers ! 0))"
    and final_low:
      "fri_table_low_degree_on
        (fri_degree_after n (fri_padded_degree_bound d))
        (fri_canonical_domain_at n)
        (fri_conditioned_layer_table n (layers ! n))"
    and sampled:
      "\<And>round_idx i.
        round_idx < length query_idxs \<Longrightarrow>
        i < n \<Longrightarrow>
        fri_evidence_next_idx roots query_idxs round_idx i <
          length (fri_canonical_domain_at i) div 2 \<and>
        fri_conditioned_layer_table (Suc i) (layers ! Suc i) !
            fri_evidence_next_idx roots query_idxs round_idx i =
          fri_table_fold_value (challenges ! i)
            (fri_conditioned_layer_table i (layers ! i))
            (fri_canonical_domain_at i)
            (length (fri_canonical_domain_at i))
            (2 ^ i)
            (fri_evidence_next_idx roots query_idxs round_idx i)"
  shows
    "challenges \<in> generic_fri_bad_challenge_lists n
        (fri_conditioned_bad_challenges d committed) \<or>
      (\<exists>i < n.
        query_idxs \<in>
          fri_conditioned_residual_query_lists roots challenges layers i)"
proof (rule ccontr)
  assume not_conclusion:
    "\<not> (challenges \<in> generic_fri_bad_challenge_lists n
          (fri_conditioned_bad_challenges d committed) \<or>
        (\<exists>i < n.
          query_idxs \<in>
            fri_conditioned_residual_query_lists roots challenges layers i))"
  then have not_bad:
      "challenges \<notin> generic_fri_bad_challenge_lists n
        (fri_conditioned_bad_challenges d committed)"
    by simp
  from not_conclusion have no_residual:
      "\<And>i. i < n \<Longrightarrow>
        query_idxs \<notin>
          fri_conditioned_residual_query_lists roots challenges layers i"
    by blast
  have not_low:
      "\<And>i. i \<le> n \<Longrightarrow>
        \<not> fri_table_low_degree_on
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i)
          (fri_conditioned_layer_table i (layers ! i))"
  proof -
    fix i
    assume i_bound: "i \<le> n"
    show
      "\<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i (layers ! i))"
      using i_bound
    proof (induction i)
      case 0
      then show ?case
        using start_not_low by simp
    next
      case (Suc i)
      have i_lt: "i < n"
        using Suc.prems by simp
      have current_not_low:
          "\<not> fri_table_low_degree_on
            (fri_degree_after i (fri_padded_degree_bound d))
            (fri_canonical_domain_at i)
            (fri_conditioned_layer_table i (layers ! i))"
        by (rule Suc.IH) (use Suc.prems in simp)
      show ?case
      proof
        assume next_low:
          "fri_table_low_degree_on
            (fri_degree_after (Suc i) (fri_padded_degree_bound d))
            (fri_canonical_domain_at (Suc i))
            (fri_conditioned_layer_table (Suc i) (layers ! Suc i))"
        have challenge_not_bad:
            "challenges ! i \<notin>
              fri_conditioned_bad_challenges d committed i
                (take i challenges)"
          by (rule fri_multiround_bad_challenge_lists_notinD[
              OF challenge_space _ i_lt])
            (use not_bad in
              \<open>simp add: generic_fri_bad_challenge_lists_def\<close>)
        have agreement_all:
            "\<forall>round_idx < length query_idxs.
              fri_evidence_next_idx roots query_idxs round_idx i \<in>
                fri_conditioned_agreement_indices i
                  (layers ! i) (layers ! Suc i) (challenges ! i)"
        proof (intro allI impI)
          fix round_idx
          assume round_idx_bound: "round_idx < length query_idxs"
          from sampled[OF round_idx_bound i_lt]
          have idx_bound:
              "fri_evidence_next_idx roots query_idxs round_idx i <
                length (fri_canonical_domain_at i) div 2"
            and sampled_value:
              "fri_conditioned_layer_table (Suc i) (layers ! Suc i) !
                  fri_evidence_next_idx roots query_idxs round_idx i =
                fri_table_fold_value (challenges ! i)
                  (fri_conditioned_layer_table i (layers ! i))
                  (fri_canonical_domain_at i)
                  (length (fri_canonical_domain_at i))
                  (2 ^ i)
                  (fri_evidence_next_idx roots query_idxs round_idx i)"
            by blast+
          have i_round: "i < ceil_log (Suc d)"
            using i_lt round_count by simp
          have cover_i:
              "length (fri_canonical_domain_at i) \<le> length (layers ! i)"
            by (rule layer_cover) (use i_lt in simp)
          have cover_suc:
              "length (fri_canonical_domain_at (Suc i)) \<le>
                length (layers ! Suc i)"
            by (rule layer_cover) (use i_lt in simp)
          have split:
              "challenges ! i \<in>
                  fri_conditioned_bad_challenges d committed i
                    (take i challenges) \<or>
                fri_evidence_next_idx roots query_idxs round_idx i \<in>
                  fri_conditioned_agreement_indices i
                    (layers ! i) (layers ! Suc i) (challenges ! i)"
            by (rule conditioned_transition_challenge_or_agreement[
                where N=N and d=d and i=i
                  and current="layers ! i"
                  and committed=committed and prefix="take i challenges"
                  and idx="fri_evidence_next_idx roots query_idxs round_idx i"
                  and b="challenges ! i",
                OF eval_power i_round rounds_le cover_i cover_suc
                  committed_path[OF i_lt] current_not_low next_low
                  idx_bound sampled_value])
          show
              "fri_evidence_next_idx roots query_idxs round_idx i \<in>
                fri_conditioned_agreement_indices i
                  (layers ! i) (layers ! Suc i) (challenges ! i)"
            using split challenge_not_bad by blast
        qed
        have residual:
            "query_idxs \<in>
              fri_conditioned_residual_query_lists roots challenges layers i"
          using agreement_all
          unfolding fri_conditioned_residual_query_lists_def by simp
        show False
          using no_residual[OF i_lt] residual by contradiction
      qed
    qed
  qed
  have final_not_low:
      "\<not> fri_table_low_degree_on
        (fri_degree_after n (fri_padded_degree_bound d))
        (fri_canonical_domain_at n)
        (fri_conditioned_layer_table n (layers ! n))"
    by (rule not_low) simp
  show False
    using final_low final_not_low by contradiction
qed

end

end
