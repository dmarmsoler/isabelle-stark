theory Soundness_FRI_RO_Actual_Query_Chain_Conflict_Collapse
  imports
    Soundness_FRI_RO_Actual_Query_Fold_Evidence
    Soundness_FRI_Composition_Replay_Gaps
    Soundness_FRI_Layer_Authenticated
begin


context soundness
begin

definition generic_fri_recorded_value_chain_evidence
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> bool"
where
  "generic_fri_recorded_value_chain_evidence roots challenges final_value
      query_idxs round_layers \<longleftrightarrow>
    length challenges = length roots \<and>
    length round_layers = length query_idxs \<and>
    (\<forall>round_idx < length query_idxs.
      \<exists>chain_values.
        length chain_values = Suc (length challenges) \<and>
        chain_values ! length challenges = final_value \<and>
        (\<forall>layer_idx < length challenges.
          \<exists>xp_path xn xn_path.
            fri_layer_step_evidence
              (roots ! layer_idx)
              (challenges ! layer_idx)
              (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
              (2 ^ layer_idx)
              (fri_sibling_index
                (fri_evidence_layer_len roots layer_idx)
                (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
              (chain_values ! layer_idx) xp_path xn xn_path
              (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
              (chain_values ! Suc layer_idx)
              (round_layers ! round_idx ! layer_idx)))"


lemma generic_fri_recorded_value_chain_evidenceE:
  assumes chain:
    "generic_fri_recorded_value_chain_evidence roots challenges final_value
      query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
  obtains chain_values where
    "length challenges = length roots"
    "length round_layers = length query_idxs"
    "length chain_values = Suc (length challenges)"
    "chain_values ! length challenges = final_value"
    "\<forall>layer_idx < length challenges.
      \<exists>xp_path xn xn_path.
        fri_layer_step_evidence
          (roots ! layer_idx)
          (challenges ! layer_idx)
          (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
          (2 ^ layer_idx)
          (fri_sibling_index
            (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
          (chain_values ! layer_idx) xp_path xn xn_path
          (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
          (chain_values ! Suc layer_idx)
          (round_layers ! round_idx ! layer_idx)"
  using chain round_bound
  unfolding generic_fri_recorded_value_chain_evidence_def
  by blast


lemma generic_fri_recorded_value_chain_forced_value_eq:
  assumes chain:
    "generic_fri_recorded_value_chain_evidence roots challenges final_value
      query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
    and forced:
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx layer_idx v"
  obtains chain_values where
    "length chain_values = Suc (length challenges)"
    "chain_values ! length challenges = final_value"
    "v = chain_values ! Suc layer_idx"
    "\<forall>j < length challenges.
      \<exists>xp_path xn xn_path.
        fri_layer_step_evidence
          (roots ! j)
          (challenges ! j)
          (fri_evidence_layer_len roots j)
          (fri_evidence_layer_idx roots query_idxs round_idx j)
          (2 ^ j)
          (fri_sibling_index
            (fri_evidence_layer_len roots j)
            (fri_evidence_layer_idx roots query_idxs round_idx j))
          (chain_values ! j) xp_path xn xn_path
          (fri_evidence_next_idx roots query_idxs round_idx j)
          (chain_values ! Suc j)
          (round_layers ! round_idx ! j)"
proof -
  from generic_fri_recorded_value_chain_evidenceE[
      OF chain round_bound]
  obtain chain_values where
    challenges_len: "length challenges = length roots"
    and round_layers_len: "length round_layers = length query_idxs"
    and chain_values_len: "length chain_values = Suc (length challenges)"
    and chain_values_final: "chain_values ! length challenges = final_value"
    and steps:
      "\<forall>j < length challenges.
        \<exists>xp_path xn xn_path.
          fri_layer_step_evidence
            (roots ! j)
            (challenges ! j)
            (fri_evidence_layer_len roots j)
            (fri_evidence_layer_idx roots query_idxs round_idx j)
            (2 ^ j)
            (fri_sibling_index
              (fri_evidence_layer_len roots j)
              (fri_evidence_layer_idx roots query_idxs round_idx j))
            (chain_values ! j) xp_path xn xn_path
            (fri_evidence_next_idx roots query_idxs round_idx j)
            (chain_values ! Suc j)
            (round_layers ! round_idx ! j)"
    .
  from steps[rule_format, OF layer_bound]
  obtain xp_path xn xn_path where step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        (chain_values ! layer_idx) xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (chain_values ! Suc layer_idx)
        (round_layers ! round_idx ! layer_idx)"
    by blast
  have value_eq: "v = chain_values ! Suc layer_idx"
    by (rule generic_fri_forced_next_value_eq_from_recorded_step[
          OF forced step])
  show ?thesis
    by (rule that[OF chain_values_len chain_values_final value_eq steps])
qed


lemma generic_fri_recorded_value_chain_successor_step:
  assumes chain:
    "generic_fri_recorded_value_chain_evidence roots challenges final_value
      query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "Suc layer_idx < length challenges"
    and forced:
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx layer_idx v"
  obtains xp_path xn xn_path where
    "fri_layer_step_evidence
      (roots ! Suc layer_idx)
      (challenges ! Suc layer_idx)
      (fri_evidence_layer_len roots (Suc layer_idx))
      (fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx))
      (2 ^ Suc layer_idx)
      (fri_sibling_index
        (fri_evidence_layer_len roots (Suc layer_idx))
        (fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx)))
      v xp_path xn xn_path
      (fri_evidence_next_idx roots query_idxs round_idx (Suc layer_idx))
      (fri_evidence_next_value roots challenges query_idxs round_idx
        (Suc layer_idx) v xn)
      (round_layers ! round_idx ! Suc layer_idx)"
proof -
  have current_bound: "layer_idx < length challenges"
    using layer_bound by simp
  from generic_fri_recorded_value_chain_forced_value_eq[
      OF chain round_bound current_bound forced]
  obtain chain_values where
    chain_values_len: "length chain_values = Suc (length challenges)"
    and chain_values_final:
      "chain_values ! length challenges = final_value"
    and value_eq: "v = chain_values ! Suc layer_idx"
    and steps:
      "\<forall>j < length challenges.
        \<exists>xp_path xn xn_path.
          fri_layer_step_evidence
            (roots ! j)
            (challenges ! j)
            (fri_evidence_layer_len roots j)
            (fri_evidence_layer_idx roots query_idxs round_idx j)
            (2 ^ j)
            (fri_sibling_index
              (fri_evidence_layer_len roots j)
              (fri_evidence_layer_idx roots query_idxs round_idx j))
            (chain_values ! j) xp_path xn xn_path
            (fri_evidence_next_idx roots query_idxs round_idx j)
            (chain_values ! Suc j)
            (round_layers ! round_idx ! j)"
    .
  from steps[rule_format, OF layer_bound]
  obtain xp_path xn xn_path where step:
      "fri_layer_step_evidence
        (roots ! Suc layer_idx)
        (challenges ! Suc layer_idx)
        (fri_evidence_layer_len roots (Suc layer_idx))
        (fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx)))
        (chain_values ! Suc layer_idx) xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx (Suc layer_idx))
        (chain_values ! Suc (Suc layer_idx))
        (round_layers ! round_idx ! Suc layer_idx)"
    by blast
  have next_eq:
      "chain_values ! Suc (Suc layer_idx) =
        fri_evidence_next_value roots challenges query_idxs round_idx
          (Suc layer_idx) (chain_values ! Suc layer_idx) xn"
    using fri_layer_step_evidenceD(3)[OF step]
    unfolding fri_evidence_next_value_def
    by simp
  have normalized:
      "fri_layer_step_evidence
        (roots ! Suc layer_idx)
        (challenges ! Suc layer_idx)
        (fri_evidence_layer_len roots (Suc layer_idx))
        (fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx)))
        v xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx (Suc layer_idx))
        (fri_evidence_next_value roots challenges query_idxs round_idx
          (Suc layer_idx) v xn)
        (round_layers ! round_idx ! Suc layer_idx)"
    using step value_eq next_eq by simp
  show ?thesis
    by (rule that[OF normalized])
qed

lemma generic_fri_recorded_value_chain_no_final_conflict:
  assumes chain:
    "generic_fri_recorded_value_chain_evidence roots challenges final_value
      query_idxs round_layers"
  shows
    "\<not> generic_fri_sampled_final_value_conflict roots challenges final_value
      query_idxs round_layers"
proof
  assume conflict:
    "generic_fri_sampled_final_value_conflict roots challenges final_value
      query_idxs round_layers"
  from generic_fri_sampled_final_value_conflictE[OF conflict]
  obtain round_idx v where
    challenges_nonempty: "0 < length challenges"
    and round_bound: "round_idx < length query_idxs"
    and forced:
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx (length challenges - 1) v"
    and value_neq: "v \<noteq> final_value"
    .
  have layer_bound: "length challenges - 1 < length challenges"
    using challenges_nonempty by simp
  from generic_fri_recorded_value_chain_forced_value_eq[
      OF chain round_bound layer_bound forced]
  obtain chain_values where
    chain_values_final:
      "chain_values ! length challenges = final_value"
    and value_eq:
      "v = chain_values ! Suc (length challenges - 1)"
    by blast
  have successor_last:
      "Suc (length challenges - 1) = length challenges"
    using challenges_nonempty by simp
  have "v = final_value"
    using value_eq chain_values_final successor_last by simp
  then show False
    using value_neq by simp
qed


lemma generic_fri_recorded_value_chain_successor_conflict_imp_same_layer:
  assumes chain:
    "generic_fri_recorded_value_chain_evidence roots challenges final_value
      query_idxs round_layers"
    and successor:
      "generic_fri_sampled_successor_opening_conflict roots challenges
        query_idxs round_layers"
  shows
    "generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
proof -
  have challenges_len: "length challenges = length roots"
    using chain
    unfolding generic_fri_recorded_value_chain_evidence_def
    by simp
  show ?thesis
  proof (rule
      generic_fri_sampled_successor_conflict_imp_same_layer_with_source_steps[
        OF successor challenges_len])
    fix source_round layer_idx v
    assume source_bound: "source_round < length query_idxs"
      and layer_bound: "Suc layer_idx < length challenges"
      and forced:
        "generic_fri_round_forced_next_value roots challenges query_idxs
          round_layers source_round layer_idx v"
    from generic_fri_recorded_value_chain_successor_step[
        OF chain source_bound layer_bound forced]
    obtain xp_path xn xn_path where
      "fri_layer_step_evidence
        (roots ! Suc layer_idx)
        (challenges ! Suc layer_idx)
        (fri_evidence_layer_len roots (Suc layer_idx))
        (fri_evidence_layer_idx roots query_idxs source_round
          (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs source_round
            (Suc layer_idx)))
        v xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs source_round
          (Suc layer_idx))
        (fri_evidence_next_value roots challenges query_idxs source_round
          (Suc layer_idx) v xn)
        (round_layers ! source_round ! Suc layer_idx)"
      .
    then show
      "\<exists>xp_path xn xn_path.
        fri_layer_step_evidence
          (roots ! Suc layer_idx)
          (challenges ! Suc layer_idx)
          (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs source_round
            (Suc layer_idx))
          (2 ^ Suc layer_idx)
          (fri_sibling_index
            (fri_evidence_layer_len roots (Suc layer_idx))
            (fri_evidence_layer_idx roots query_idxs source_round
              (Suc layer_idx)))
          v xp_path xn xn_path
          (fri_evidence_next_idx roots query_idxs source_round
            (Suc layer_idx))
          (fri_evidence_next_value roots challenges query_idxs source_round
            (Suc layer_idx) v xn)
          (round_layers ! source_round ! Suc layer_idx)"
      by blast
  qed
qed


lemma generic_fri_recorded_value_chain_next_conflict_imp_same_layer:
  assumes chain:
    "generic_fri_recorded_value_chain_evidence roots challenges final_value
      query_idxs round_layers"
    and next_conflict:
      "generic_fri_sampled_next_value_conflict roots challenges query_idxs
        round_layers"
  shows
    "generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
proof -
  from generic_fri_sampled_next_value_conflictE[OF next_conflict]
  obtain round_idx round_idx' layer_idx v v' where
    round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
    and same_next:
      "fri_evidence_next_idx roots query_idxs round_idx layer_idx =
        fri_evidence_next_idx roots query_idxs round_idx' layer_idx"
    and forced:
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx layer_idx v"
    and forced':
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx' layer_idx v'"
    and value_neq: "v \<noteq> v'"
    .
  have challenges_len: "length challenges = length roots"
    using chain
    unfolding generic_fri_recorded_value_chain_evidence_def
    by simp
  show ?thesis
  proof (cases "Suc layer_idx < length challenges")
    case True
    from generic_fri_recorded_value_chain_successor_step[
        OF chain round_bound True forced]
    obtain v_path vn vn_path where source_step:
      "fri_layer_step_evidence
        (roots ! Suc layer_idx)
        (challenges ! Suc layer_idx)
        (fri_evidence_layer_len roots (Suc layer_idx))
        (fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs round_idx
            (Suc layer_idx)))
        v v_path vn vn_path
        (fri_evidence_next_idx roots query_idxs round_idx (Suc layer_idx))
        (fri_evidence_next_value roots challenges query_idxs round_idx
          (Suc layer_idx) v vn)
        (round_layers ! round_idx ! Suc layer_idx)"
      .
    from generic_fri_recorded_value_chain_successor_step[
        OF chain round_bound' True forced']
    obtain v'_path vn' vn'_path where target_step:
      "fri_layer_step_evidence
        (roots ! Suc layer_idx)
        (challenges ! Suc layer_idx)
        (fri_evidence_layer_len roots (Suc layer_idx))
        (fri_evidence_layer_idx roots query_idxs round_idx' (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs round_idx'
            (Suc layer_idx)))
        v' v'_path vn' vn'_path
        (fri_evidence_next_idx roots query_idxs round_idx' (Suc layer_idx))
        (fri_evidence_next_value roots challenges query_idxs round_idx'
          (Suc layer_idx) v' vn')
        (round_layers ! round_idx' ! Suc layer_idx)"
      .
    have source_idx:
        "fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx) =
          fri_evidence_next_idx roots query_idxs round_idx layer_idx"
      by (rule fri_evidence_layer_idx_Suc)
        (use True challenges_len in simp)
    have target_idx:
        "fri_evidence_layer_idx roots query_idxs round_idx' (Suc layer_idx) =
          fri_evidence_next_idx roots query_idxs round_idx' layer_idx"
      by (rule fri_evidence_layer_idx_Suc)
        (use True challenges_len in simp)
    have same_idx:
        "fri_evidence_layer_idx roots query_idxs round_idx (Suc layer_idx) =
          fri_evidence_layer_idx roots query_idxs round_idx' (Suc layer_idx)"
      using same_next source_idx target_idx by simp
    show ?thesis
      unfolding generic_fri_sampled_same_layer_opening_conflict_def
      apply (rule exI[where x=round_idx])
      apply (rule exI[where x=round_idx'])
      apply (rule exI[where x="Suc layer_idx"])
      apply (rule exI[where x=v])
      apply (rule exI[where x=v_path])
      apply (rule exI[where x=vn])
      apply (rule exI[where x=vn_path])
      apply (rule exI[where x=v'])
      apply (rule exI[where x=v'_path])
      apply (rule exI[where x=vn'])
      apply (rule exI[where x=vn'_path])
      using round_bound round_bound' True source_step target_step
        same_idx value_neq
      by blast
  next
    case False
    have layer_last: "layer_idx = length challenges - 1"
      using layer_bound False by linarith
    from generic_fri_recorded_value_chain_forced_value_eq[
        OF chain round_bound layer_bound forced]
    obtain chain_values where
      chain_values_final:
        "chain_values ! length challenges = final_value"
      and value_eq: "v = chain_values ! Suc layer_idx"
      by blast
    from generic_fri_recorded_value_chain_forced_value_eq[
        OF chain round_bound' layer_bound forced']
    obtain chain_values' where
      chain_values_final':
        "chain_values' ! length challenges = final_value"
      and value_eq': "v' = chain_values' ! Suc layer_idx"
      by blast
    have challenges_nonempty: "0 < length challenges"
      using layer_bound by linarith
    have successor_last: "Suc layer_idx = length challenges"
      using layer_last challenges_nonempty by simp
    have "v = final_value"
      using value_eq chain_values_final successor_last by simp
    moreover have "v' = final_value"
      using value_eq' chain_values_final' successor_last by simp
    ultimately show ?thesis
      using value_neq by simp
  qed
qed


lemma generic_fri_recorded_value_chain_assignment_conflict_imp_base_or_same:
  assumes chain:
    "generic_fri_recorded_value_chain_evidence roots challenges final_value
      query_idxs round_layers"
    and conflict:
      "generic_fri_sampled_assignment_conflict candidate_table roots
        challenges final_value query_idxs round_layers"
  shows
    "generic_fri_sampled_base_opening_conflict candidate_table roots
       challenges query_idxs round_layers \<or>
     generic_fri_sampled_same_layer_opening_conflict roots challenges
       query_idxs round_layers"
proof -
  have next_imp:
      "generic_fri_sampled_next_value_conflict roots challenges query_idxs
        round_layers \<Longrightarrow>
       generic_fri_sampled_same_layer_opening_conflict roots challenges
        query_idxs round_layers"
    by (rule generic_fri_recorded_value_chain_next_conflict_imp_same_layer[
          OF chain])
  have successor_imp:
      "generic_fri_sampled_successor_opening_conflict roots challenges
        query_idxs round_layers \<Longrightarrow>
       generic_fri_sampled_same_layer_opening_conflict roots challenges
        query_idxs round_layers"
    by (rule
      generic_fri_recorded_value_chain_successor_conflict_imp_same_layer[
        OF chain])
  have no_final:
      "\<not> generic_fri_sampled_final_value_conflict roots challenges
        final_value query_idxs round_layers"
    by (rule generic_fri_recorded_value_chain_no_final_conflict[OF chain])
  show ?thesis
    using conflict next_imp successor_imp no_final
    unfolding generic_fri_sampled_assignment_conflict_def
    by blast
qed


lemma ro_recorded_query_fri_accepted_evidence_all_value_chains:
  assumes trace_layers_len:
      "length trace_round_layers = length raws"
    and composition_layers_len:
      "length composition_round_layers = length raws"
    and accepted:
      "\<forall>round_idx < length raws.
        ro_recorded_query_fri_accepted_evidence
          fr f_fl f_final as fl final (raws ! round_idx)
          (trace_round_layers ! round_idx)
          (composition_round_layers ! round_idx) final_state"
  shows
    "generic_fri_recorded_value_chain_evidence
       (map snd f_fl) (map fst f_fl) f_final
       (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers \<and>
     generic_fri_recorded_value_chain_evidence
       (map snd fl) (map fst fl) final
       (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
proof
  show
    "generic_fri_recorded_value_chain_evidence
      (map snd f_fl) (map fst f_fl) f_final
      (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers"
    unfolding generic_fri_recorded_value_chain_evidence_def
  proof (intro conjI)
    show "length (map fst f_fl) = length (map snd f_fl)"
      by simp
    show
      "length trace_round_layers =
        length (map (\<lambda>raw. index (to_nat raw)) raws)"
      using trace_layers_len by simp
    show
      "\<forall>round_idx < length (map (\<lambda>raw. index (to_nat raw)) raws).
        \<exists>chain_values.
          length chain_values = Suc (length (map fst f_fl)) \<and>
          chain_values ! length (map fst f_fl) = f_final \<and>
          (\<forall>layer_idx < length (map fst f_fl).
            \<exists>xp_path xn xn_path.
              fri_layer_step_evidence
                (map snd f_fl ! layer_idx)
                (map fst f_fl ! layer_idx)
                (fri_evidence_layer_len (map snd f_fl) layer_idx)
                (fri_evidence_layer_idx (map snd f_fl)
                  (map (\<lambda>raw. index (to_nat raw)) raws)
                  round_idx layer_idx)
                (2 ^ layer_idx)
                (fri_sibling_index
                  (fri_evidence_layer_len (map snd f_fl) layer_idx)
                  (fri_evidence_layer_idx (map snd f_fl)
                    (map (\<lambda>raw. index (to_nat raw)) raws)
                    round_idx layer_idx))
                (chain_values ! layer_idx) xp_path xn xn_path
                (fri_evidence_next_idx (map snd f_fl)
                  (map (\<lambda>raw. index (to_nat raw)) raws)
                  round_idx layer_idx)
                (chain_values ! Suc layer_idx)
                (trace_round_layers ! round_idx ! layer_idx))"
    proof (intro allI impI)
      fix round_idx
      assume round_bound:
        "round_idx < length (map (\<lambda>raw. index (to_nat raw)) raws)"
      then have raw_bound: "round_idx < length raws"
        by simp
      have accepted_round:
          "ro_recorded_query_fri_accepted_evidence
            fr f_fl f_final as fl final (raws ! round_idx)
            (trace_round_layers ! round_idx)
            (composition_round_layers ! round_idx) final_state"
        by (rule accepted[rule_format, OF raw_bound])
      from ro_recorded_query_fri_accepted_evidence_recorded_chains[
          OF accepted_round]
      obtain fv where trace_chain:
        "ro_fri_fold_recorded_chain_evidence
          f_fl (index (to_nat (raws ! round_idx))) (hd fv)
          (clength * scale) 1 (trace_round_layers ! round_idx) f_final"
        .
      from trace_chain obtain chain_values where
        chain_values_len: "length chain_values = Suc (length f_fl)"
        and chain_values_final: "chain_values ! length f_fl = f_final"
        and steps:
          "\<forall>layer_idx < length f_fl.
            \<exists>xp_path xn xn_path.
              fri_layer_step_evidence
                (snd (f_fl ! layer_idx))
                (fst (f_fl ! layer_idx))
                (fri_layer_lengths (length f_fl) (clength * scale) !
                  layer_idx)
                (fri_layer_indices (length f_fl)
                  (index (to_nat (raws ! round_idx)))
                  (clength * scale) ! layer_idx)
                (1 * 2 ^ layer_idx)
                (fri_sibling_index
                  (fri_layer_lengths (length f_fl) (clength * scale) !
                    layer_idx)
                  (fri_layer_indices (length f_fl)
                    (index (to_nat (raws ! round_idx)))
                    (clength * scale) ! layer_idx))
                (chain_values ! layer_idx) xp_path xn xn_path
                (fri_layer_indices (length f_fl)
                  (index (to_nat (raws ! round_idx)))
                  (clength * scale) ! layer_idx mod
                  (fri_layer_lengths (length f_fl) (clength * scale) !
                    layer_idx div 2))
                (chain_values ! Suc layer_idx)
                (trace_round_layers ! round_idx ! layer_idx)"
        unfolding ro_fri_fold_recorded_chain_evidence_def
        by blast
      show
        "\<exists>chain_values.
          length chain_values = Suc (length (map fst f_fl)) \<and>
          chain_values ! length (map fst f_fl) = f_final \<and>
          (\<forall>layer_idx < length (map fst f_fl).
            \<exists>xp_path xn xn_path.
              fri_layer_step_evidence
                (map snd f_fl ! layer_idx)
                (map fst f_fl ! layer_idx)
                (fri_evidence_layer_len (map snd f_fl) layer_idx)
                (fri_evidence_layer_idx (map snd f_fl)
                  (map (\<lambda>raw. index (to_nat raw)) raws)
                  round_idx layer_idx)
                (2 ^ layer_idx)
                (fri_sibling_index
                  (fri_evidence_layer_len (map snd f_fl) layer_idx)
                  (fri_evidence_layer_idx (map snd f_fl)
                    (map (\<lambda>raw. index (to_nat raw)) raws)
                    round_idx layer_idx))
                (chain_values ! layer_idx) xp_path xn xn_path
                (fri_evidence_next_idx (map snd f_fl)
                  (map (\<lambda>raw. index (to_nat raw)) raws)
                  round_idx layer_idx)
                (chain_values ! Suc layer_idx)
                (trace_round_layers ! round_idx ! layer_idx))"
        apply (rule exI[where x=chain_values])
        using chain_values_len chain_values_final steps raw_bound
        unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
          fri_evidence_next_idx_def
        by simp
    qed
  qed
  show
    "generic_fri_recorded_value_chain_evidence
      (map snd fl) (map fst fl) final
      (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    unfolding generic_fri_recorded_value_chain_evidence_def
  proof (intro conjI)
    show "length (map fst fl) = length (map snd fl)"
      by simp
    show
      "length composition_round_layers =
        length (map (\<lambda>raw. index (to_nat raw)) raws)"
      using composition_layers_len by simp
    show
      "\<forall>round_idx < length (map (\<lambda>raw. index (to_nat raw)) raws).
        \<exists>chain_values.
          length chain_values = Suc (length (map fst fl)) \<and>
          chain_values ! length (map fst fl) = final \<and>
          (\<forall>layer_idx < length (map fst fl).
            \<exists>xp_path xn xn_path.
              fri_layer_step_evidence
                (map snd fl ! layer_idx)
                (map fst fl ! layer_idx)
                (fri_evidence_layer_len (map snd fl) layer_idx)
                (fri_evidence_layer_idx (map snd fl)
                  (map (\<lambda>raw. index (to_nat raw)) raws)
                  round_idx layer_idx)
                (2 ^ layer_idx)
                (fri_sibling_index
                  (fri_evidence_layer_len (map snd fl) layer_idx)
                  (fri_evidence_layer_idx (map snd fl)
                    (map (\<lambda>raw. index (to_nat raw)) raws)
                    round_idx layer_idx))
                (chain_values ! layer_idx) xp_path xn xn_path
                (fri_evidence_next_idx (map snd fl)
                  (map (\<lambda>raw. index (to_nat raw)) raws)
                  round_idx layer_idx)
                (chain_values ! Suc layer_idx)
                (composition_round_layers ! round_idx ! layer_idx))"
    proof (intro allI impI)
      fix round_idx
      assume round_bound:
        "round_idx < length (map (\<lambda>raw. index (to_nat raw)) raws)"
      then have raw_bound: "round_idx < length raws"
        by simp
      have accepted_round:
          "ro_recorded_query_fri_accepted_evidence
            fr f_fl f_final as fl final (raws ! round_idx)
            (trace_round_layers ! round_idx)
            (composition_round_layers ! round_idx) final_state"
        by (rule accepted[rule_format, OF raw_bound])
      from ro_recorded_query_fri_accepted_evidence_recorded_chains[
          OF accepted_round]
      obtain fv where composition_chain:
        "ro_fri_fold_recorded_chain_evidence
          fl (index (to_nat (raws ! round_idx)))
          (cp_eval as fv (h ^ index (to_nat (raws ! round_idx)) * shift))
          (clength * scale) 1
          (composition_round_layers ! round_idx) final"
        .
      from composition_chain obtain chain_values where
        chain_values_len: "length chain_values = Suc (length fl)"
        and chain_values_final: "chain_values ! length fl = final"
        and steps:
          "\<forall>layer_idx < length fl.
            \<exists>xp_path xn xn_path.
              fri_layer_step_evidence
                (snd (fl ! layer_idx))
                (fst (fl ! layer_idx))
                (fri_layer_lengths (length fl) (clength * scale) ! layer_idx)
                (fri_layer_indices (length fl)
                  (index (to_nat (raws ! round_idx)))
                  (clength * scale) ! layer_idx)
                (1 * 2 ^ layer_idx)
                (fri_sibling_index
                  (fri_layer_lengths (length fl) (clength * scale) !
                    layer_idx)
                  (fri_layer_indices (length fl)
                    (index (to_nat (raws ! round_idx)))
                    (clength * scale) ! layer_idx))
                (chain_values ! layer_idx) xp_path xn xn_path
                (fri_layer_indices (length fl)
                  (index (to_nat (raws ! round_idx)))
                  (clength * scale) ! layer_idx mod
                  (fri_layer_lengths (length fl) (clength * scale) !
                    layer_idx div 2))
                (chain_values ! Suc layer_idx)
                (composition_round_layers ! round_idx ! layer_idx)"
        unfolding ro_fri_fold_recorded_chain_evidence_def
        by blast
      show
        "\<exists>chain_values.
          length chain_values = Suc (length (map fst fl)) \<and>
          chain_values ! length (map fst fl) = final \<and>
          (\<forall>layer_idx < length (map fst fl).
            \<exists>xp_path xn xn_path.
              fri_layer_step_evidence
                (map snd fl ! layer_idx)
                (map fst fl ! layer_idx)
                (fri_evidence_layer_len (map snd fl) layer_idx)
                (fri_evidence_layer_idx (map snd fl)
                  (map (\<lambda>raw. index (to_nat raw)) raws)
                  round_idx layer_idx)
                (2 ^ layer_idx)
                (fri_sibling_index
                  (fri_evidence_layer_len (map snd fl) layer_idx)
                  (fri_evidence_layer_idx (map snd fl)
                    (map (\<lambda>raw. index (to_nat raw)) raws)
                    round_idx layer_idx))
                (chain_values ! layer_idx) xp_path xn xn_path
                (fri_evidence_next_idx (map snd fl)
                  (map (\<lambda>raw. index (to_nat raw)) raws)
                  round_idx layer_idx)
                (chain_values ! Suc layer_idx)
                (composition_round_layers ! round_idx ! layer_idx))"
        apply (rule exI[where x=chain_values])
        using chain_values_len chain_values_final steps raw_bound
        unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
          fri_evidence_next_idx_def
        by simp
    qed
  qed
qed


definition generic_fri_recorded_chunks_authenticated
  :: "'f list \<Rightarrow> nat list \<Rightarrow> 'f list list list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "generic_fri_recorded_chunks_authenticated roots query_idxs round_layers
      final_state \<longleftrightarrow>
    length round_layers = length query_idxs \<and>
    (\<forall>round_idx < length query_idxs. \<forall>layer_idx < length roots.
      fri_layer_chunk_authenticated
        (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (round_layers ! round_idx ! layer_idx) final_state)"


lemma generic_fri_recorded_chunks_authenticated_same_layer_imp_partial_merkle:
  assumes auth:
      "generic_fri_recorded_chunks_authenticated roots query_idxs
        round_layers final_state"
    and conflict:
      "generic_fri_sampled_same_layer_opening_conflict roots challenges
        query_idxs round_layers"
    and len_challenges: "length challenges = length roots"
  shows "partial_merkle_inconsistency_bad s (Some (result, final_state))"
proof -
  from conflict obtain round_idx round_idx' layer_idx
      xp xp_path xn xn_path yp yp_path yn yn_path where witness:
      "round_idx < length query_idxs \<and>
       round_idx' < length query_idxs \<and>
       layer_idx < length challenges \<and>
       fri_layer_step_evidence
         (roots ! layer_idx)
         (challenges ! layer_idx)
         (fri_evidence_layer_len roots layer_idx)
         (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
         (2 ^ layer_idx)
         (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
           (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
         xp xp_path xn xn_path
         (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
         (fri_evidence_next_value roots challenges query_idxs round_idx
           layer_idx xp xn)
         (round_layers ! round_idx ! layer_idx) \<and>
       fri_layer_step_evidence
         (roots ! layer_idx)
         (challenges ! layer_idx)
         (fri_evidence_layer_len roots layer_idx)
         (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
         (2 ^ layer_idx)
         (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
           (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
         yp yp_path yn yn_path
         (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
         (fri_evidence_next_value roots challenges query_idxs round_idx'
           layer_idx yp yn)
         (round_layers ! round_idx' ! layer_idx) \<and>
       ((fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
           fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
         xp \<noteq> yp) \<or>
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
           fri_sibling_index (fri_evidence_layer_len roots layer_idx)
             (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
         xp \<noteq> yn) \<or>
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
           (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
           fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
         xn \<noteq> yp) \<or>
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
           (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
           fri_sibling_index (fri_evidence_layer_len roots layer_idx)
             (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
         xn \<noteq> yn))"
    unfolding generic_fri_sampled_same_layer_opening_conflict_def
    by blast
  have layer_bound_roots: "layer_idx < length roots"
    using witness len_challenges by simp
  have auth_chunk:
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (round_layers ! round_idx ! layer_idx) final_state"
    using auth witness layer_bound_roots
    unfolding generic_fri_recorded_chunks_authenticated_def
    by blast
  have auth_chunk':
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (round_layers ! round_idx' ! layer_idx) final_state"
    using auth witness layer_bound_roots
    unfolding generic_fri_recorded_chunks_authenticated_def
    by blast
  have auth_conflict:
      "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        roots challenges query_idxs round_layers final_state"
    unfolding
      generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_def
    apply (rule exI[where x=round_idx])
    apply (rule exI[where x=round_idx'])
    apply (rule exI[where x=layer_idx])
    apply (rule exI[where x=xp])
    apply (rule exI[where x=xp_path])
    apply (rule exI[where x=xn])
    apply (rule exI[where x=xn_path])
    apply (rule exI[where x=yp])
    apply (rule exI[where x=yp_path])
    apply (rule exI[where x=yn])
    apply (rule exI[where x=yn_path])
    using witness auth_chunk auth_chunk'
    by blast
  show ?thesis
    by (rule
      generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_imp_partial_merkle[
        OF auth_conflict len_challenges])
qed


lemma generic_fri_recorded_chain_assignment_conflict_imp_base_or_partial_merkle:
  assumes chain:
      "generic_fri_recorded_value_chain_evidence roots challenges final_value
        query_idxs round_layers"
    and auth:
      "generic_fri_recorded_chunks_authenticated roots query_idxs
        round_layers final_state"
    and conflict:
      "generic_fri_sampled_assignment_conflict candidate_table roots
        challenges final_value query_idxs round_layers"
  shows
    "generic_fri_sampled_base_opening_conflict candidate_table roots
       challenges query_idxs round_layers \<or>
     partial_merkle_inconsistency_bad s (Some (result, final_state))"
proof -
  have len_challenges: "length challenges = length roots"
    using chain
    unfolding generic_fri_recorded_value_chain_evidence_def
    by simp
  have base_or_same:
      "generic_fri_sampled_base_opening_conflict candidate_table roots
         challenges query_idxs round_layers \<or>
       generic_fri_sampled_same_layer_opening_conflict roots challenges
         query_idxs round_layers"
    by (rule
      generic_fri_recorded_value_chain_assignment_conflict_imp_base_or_same[
        OF chain conflict])
  from base_or_same show ?thesis
  proof
    assume
      "generic_fri_sampled_base_opening_conflict candidate_table roots
        challenges query_idxs round_layers"
    then show ?thesis by simp
  next
    assume same:
      "generic_fri_sampled_same_layer_opening_conflict roots challenges
        query_idxs round_layers"
    have "partial_merkle_inconsistency_bad s (Some (result, final_state))"
      by (rule
        generic_fri_recorded_chunks_authenticated_same_layer_imp_partial_merkle[
          OF auth same len_challenges])
    then show ?thesis by simp
  qed
qed


lemma ro_recorded_query_fri_accepted_evidence_all_chunks_authenticated:
  assumes trace_layers_len:
      "length trace_round_layers = length raws"
    and composition_layers_len:
      "length composition_round_layers = length raws"
    and accepted:
      "\<forall>round_idx < length raws.
        ro_recorded_query_fri_accepted_evidence
          fr f_fl f_final as fl final (raws ! round_idx)
          (trace_round_layers ! round_idx)
          (composition_round_layers ! round_idx) final_state"
  shows
    "generic_fri_recorded_chunks_authenticated
       (map snd f_fl) (map (\<lambda>raw. index (to_nat raw)) raws)
       trace_round_layers final_state \<and>
     generic_fri_recorded_chunks_authenticated
       (map snd fl) (map (\<lambda>raw. index (to_nat raw)) raws)
       composition_round_layers final_state"
proof
  show
    "generic_fri_recorded_chunks_authenticated
      (map snd f_fl) (map (\<lambda>raw. index (to_nat raw)) raws)
      trace_round_layers final_state"
    unfolding generic_fri_recorded_chunks_authenticated_def
  proof (intro conjI)
    show
      "length trace_round_layers =
        length (map (\<lambda>raw. index (to_nat raw)) raws)"
      using trace_layers_len by simp
    show
      "\<forall>round_idx < length (map (\<lambda>raw. index (to_nat raw)) raws).
        \<forall>layer_idx < length (map snd f_fl).
          fri_layer_chunk_authenticated
            (map snd f_fl ! layer_idx)
            (fri_evidence_layer_len (map snd f_fl) layer_idx)
            (fri_evidence_layer_idx (map snd f_fl)
              (map (\<lambda>raw. index (to_nat raw)) raws)
              round_idx layer_idx)
            (trace_round_layers ! round_idx ! layer_idx) final_state"
    proof (intro allI impI)
      fix round_idx layer_idx
      assume round_bound:
          "round_idx < length (map (\<lambda>raw. index (to_nat raw)) raws)"
        and layer_bound: "layer_idx < length (map snd f_fl)"
      then have raw_bound: "round_idx < length raws"
        by simp
      have accepted_round:
          "ro_recorded_query_fri_accepted_evidence
            fr f_fl f_final as fl final (raws ! round_idx)
            (trace_round_layers ! round_idx)
            (composition_round_layers ! round_idx) final_state"
        by (rule accepted[rule_format, OF raw_bound])
      have trace_auth:
          "\<forall>j < length f_fl.
            fri_layer_chunk_authenticated ((map snd f_fl) ! j)
              (fri_layer_lengths (length f_fl) (clength * scale) ! j)
              (fri_layer_indices (length f_fl)
                (index (to_nat (raws ! round_idx)))
                (clength * scale) ! j)
              (trace_round_layers ! round_idx ! j) final_state"
        using accepted_round
        unfolding ro_recorded_query_fri_accepted_evidence_def
        by blast
      show
        "fri_layer_chunk_authenticated
          (map snd f_fl ! layer_idx)
          (fri_evidence_layer_len (map snd f_fl) layer_idx)
          (fri_evidence_layer_idx (map snd f_fl)
            (map (\<lambda>raw. index (to_nat raw)) raws)
            round_idx layer_idx)
          (trace_round_layers ! round_idx ! layer_idx) final_state"
        using trace_auth[rule_format, of layer_idx] layer_bound raw_bound
        unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
        by simp
    qed
  qed
  show
    "generic_fri_recorded_chunks_authenticated
      (map snd fl) (map (\<lambda>raw. index (to_nat raw)) raws)
      composition_round_layers final_state"
    unfolding generic_fri_recorded_chunks_authenticated_def
  proof (intro conjI)
    show
      "length composition_round_layers =
        length (map (\<lambda>raw. index (to_nat raw)) raws)"
      using composition_layers_len by simp
    show
      "\<forall>round_idx < length (map (\<lambda>raw. index (to_nat raw)) raws).
        \<forall>layer_idx < length (map snd fl).
          fri_layer_chunk_authenticated
            (map snd fl ! layer_idx)
            (fri_evidence_layer_len (map snd fl) layer_idx)
            (fri_evidence_layer_idx (map snd fl)
              (map (\<lambda>raw. index (to_nat raw)) raws)
              round_idx layer_idx)
            (composition_round_layers ! round_idx ! layer_idx) final_state"
    proof (intro allI impI)
      fix round_idx layer_idx
      assume round_bound:
          "round_idx < length (map (\<lambda>raw. index (to_nat raw)) raws)"
        and layer_bound: "layer_idx < length (map snd fl)"
      then have raw_bound: "round_idx < length raws"
        by simp
      have accepted_round:
          "ro_recorded_query_fri_accepted_evidence
            fr f_fl f_final as fl final (raws ! round_idx)
            (trace_round_layers ! round_idx)
            (composition_round_layers ! round_idx) final_state"
        by (rule accepted[rule_format, OF raw_bound])
      have composition_auth:
          "\<forall>j < length fl.
            fri_layer_chunk_authenticated ((map snd fl) ! j)
              (fri_layer_lengths (length fl) (clength * scale) ! j)
              (fri_layer_indices (length fl)
                (index (to_nat (raws ! round_idx)))
                (clength * scale) ! j)
              (composition_round_layers ! round_idx ! j) final_state"
        using accepted_round
        unfolding ro_recorded_query_fri_accepted_evidence_def
        by blast
      show
        "fri_layer_chunk_authenticated
          (map snd fl ! layer_idx)
          (fri_evidence_layer_len (map snd fl) layer_idx)
          (fri_evidence_layer_idx (map snd fl)
            (map (\<lambda>raw. index (to_nat raw)) raws)
            round_idx layer_idx)
          (composition_round_layers ! round_idx ! layer_idx) final_state"
        using composition_auth[rule_format, of layer_idx] layer_bound raw_bound
        unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
        by simp
    qed
  qed
qed


end
end
