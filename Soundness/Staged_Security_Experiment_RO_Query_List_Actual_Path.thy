(*  Title:      Stark/Staged_Security_Experiment_RO_Query_List_Actual_Path.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_RO_Query_List_Actual_Path
  imports Staged_Security_Experiment_RO_Query_List_Transcript_Product
begin

context soundness
begin

definition
  ro_absorb_checked_staged_security_experiment_with_query_witnesses
  :: "'f staged_adversary \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel \<times>
          'f list \<times> 'f protocol_channel list) \<times>
         'f protocol_channel) \<times> unit list,
       'f protocol_channel) state_monad"
where
  "ro_absorb_checked_staged_security_experiment_with_query_witnesses A =
    do {
      (data, query_start, raws, query_states) \<leftarrow>
        ro_checked_staged_transcript_program_with_query_witnesses A;
      attacker_state \<leftarrow> get;
      put
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data));
      result \<leftarrow> ro_verify_monad;
      return
        (((data, query_start, raws, query_states), attacker_state), result)
    }"

lemma
  ro_absorb_checked_staged_security_experiment_with_query_witnesses_projection:
  "ro_absorb_checked_staged_security_experiment_with_query_witnesses A \<bind>
      (\<lambda>(((data, query_start, raws, query_states), attacker_state), result).
        return ((data, attacker_state), result)) =
    ro_absorb_checked_staged_security_experiment_with_data_state A"
proof -
  have projection':
    "ro_checked_staged_transcript_program_with_query_witnesses A \<bind>
        (\<lambda>x. return (fst x)) =
      ro_checked_staged_transcript_program A"
    using
      ro_checked_staged_transcript_program_with_query_witnesses_projection[of A]
    by (simp add: split_def)
  let ?K =
    "\<lambda>data.
      get \<bind> (\<lambda>s.
        put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
        (\<lambda>_. ro_verify_monad \<bind>
          (\<lambda>result. return ((data, s), result))))"
  have
    "ro_checked_staged_transcript_program_with_query_witnesses A \<bind>
        (\<lambda>x. ?K (fst x)) =
      (ro_checked_staged_transcript_program_with_query_witnesses A \<bind>
        (\<lambda>x. return (fst x))) \<bind> ?K"
    by (simp add: sm_bind_assoc)
  also have "... = ro_checked_staged_transcript_program A \<bind> ?K"
    by (simp only: projection')
  finally show ?thesis
    unfolding
      ro_absorb_checked_staged_security_experiment_with_query_witnesses_def
      ro_absorb_checked_staged_security_experiment_with_data_state_def
    by (simp add: sm_bind_assoc split_def)
qed

definition
  ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
  :: "nat list set \<Rightarrow>
      (((('f staged_proof_data \<times> 'f protocol_channel \<times>
          'f list \<times> 'f protocol_channel list) \<times>
         'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
      Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some ((((data, query_start, raws, query_states), attacker_state), result),
          final_state) \<Rightarrow>
        map (\<lambda>raw. index (to_nat raw)) raws \<in> Q)"

definition
  ro_absorb_checked_staged_security_with_query_witnesses_actual_fresh_hit
  :: "nat list set \<Rightarrow>
      (((('f staged_proof_data \<times> 'f protocol_channel \<times>
          'f list \<times> 'f protocol_channel list) \<times>
         'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "ro_absorb_checked_staged_security_with_query_witnesses_actual_fresh_hit
      Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some ((((data, query_start, raws, query_states), attacker_state), result),
          final_state) \<Rightarrow>
        ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
          Q (Some ((data, query_start, raws, query_states), attacker_state)))"

definition
  ro_absorb_checked_staged_security_with_query_witnesses_prequery_hit
  :: "'f staged_adversary \<Rightarrow> nat list set \<Rightarrow>
      (((('f staged_proof_data \<times> 'f protocol_channel \<times>
          'f list \<times> 'f protocol_channel list) \<times>
         'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "ro_absorb_checked_staged_security_with_query_witnesses_prequery_hit A Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some ((((data, query_start, raws, query_states), attacker_state), result),
          final_state) \<Rightarrow>
        ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit
          A Q (Some (((data, attacker_state), result), final_state)))"

lemma
  ro_absorb_checked_staged_security_experiment_with_query_witnesses_outcomeE:
  assumes outcome:
    "Some ((((data, query_start, raws, query_states), attacker_state), result),
        final_state) \<in>
      set_dist
        (execute
          (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
          initial_state)"
  obtains
    "Some ((data, query_start, raws, query_states), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_query_witnesses A)
          initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute ro_verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
  using outcome
  unfolding
    ro_absorb_checked_staged_security_experiment_with_query_witnesses_def
  by (auto elim!: set_dist_bindE intro: that)

lemma
  wp_ro_absorb_checked_staged_security_experiment_with_query_witnesses_actual_fresh_bound:
  "wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (ro_absorb_checked_staged_security_with_query_witnesses_actual_fresh_hit Q)
      s \<le>
    nnreal (card (query_index_raw_list_preimage Q)) *
      (1 / nnreal size) ^ rounds"
  unfolding
    ro_absorb_checked_staged_security_experiment_with_query_witnesses_def
proof (rule wp_event_bind_bound_by_head_event)
  show
    "wp_event
        (ro_checked_staged_transcript_program_with_query_witnesses A)
        (ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
          Q)
        s \<le>
      nnreal (card (query_index_raw_list_preimage Q)) *
        (1 / nnreal size) ^ rounds"
    by (rule
        wp_ro_checked_staged_transcript_program_with_query_witnesses_query_index_list_fresh_bound)
next
  show
    "ro_absorb_checked_staged_security_with_query_witnesses_actual_fresh_hit
        Q None \<Longrightarrow>
      ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
        Q None"
    unfolding
      ro_absorb_checked_staged_security_with_query_witnesses_actual_fresh_hit_def
    by simp
next
  fix x t out
  assume head:
    "Some (x, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_query_witnesses A) s)"
  obtain data query_start raws query_states where x_eq:
    "x = (data, query_start, raws, query_states)"
    by (cases x) auto
  assume tail:
    "out \<in>
      set_dist
        (execute
          (case x of
            (data, query_start, raws, query_states) \<Rightarrow>
              get \<bind>
              (\<lambda>attacker_state.
                put
                  (verifier_state_from_adversary attacker_state
                    (staged_proof_transcript data)) \<bind>
                (\<lambda>_. ro_verify_monad \<bind>
                  (\<lambda>result.
                    return
                      (((data, query_start, raws, query_states),
                        attacker_state), result)))))
          t)"
    and fresh:
      "ro_absorb_checked_staged_security_with_query_witnesses_actual_fresh_hit
        Q out"
  show
    "ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
      Q (Some (x, t))"
    using tail fresh
    unfolding x_eq
      ro_absorb_checked_staged_security_with_query_witnesses_actual_fresh_hit_def
    by (auto simp: wpsimps elim!: set_dist_bindE
        split: option.splits prod.splits)
qed

lemma
  wp_ro_absorb_checked_staged_security_experiment_with_query_witnesses_prequery_eq:
  "wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (ro_absorb_checked_staged_security_with_query_witnesses_prequery_hit A Q)
      s =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_data_state A)
      (ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit
        A Q)
      s"
proof -
  let ?project =
    "\<lambda>(((data, query_start, raws, query_states), attacker_state), result).
      ((data, attacker_state), result)"
  let ?old =
    "ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit
      A Q"
  have event_map:
    "(\<lambda>out. case out of
      None \<Rightarrow> ?old None
    | Some (x, t) \<Rightarrow> ?old (Some (?project x, t))) =
      ro_absorb_checked_staged_security_with_query_witnesses_prequery_hit A Q"
    by (rule ext)
      (auto simp:
        ro_absorb_checked_staged_security_with_query_witnesses_prequery_hit_def
        ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit_def
        split: option.splits prod.splits)
  have mapped:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A \<bind>
        (\<lambda>x. return (?project x)))
      ?old s =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (ro_absorb_checked_staged_security_with_query_witnesses_prequery_hit A Q)
      s"
    by (subst wp_event_bind_return_map) (simp only: event_map)
  have projection:
    "ro_absorb_checked_staged_security_experiment_with_query_witnesses A \<bind>
        (\<lambda>x. return (?project x)) =
      ro_absorb_checked_staged_security_experiment_with_data_state A"
    using
      ro_absorb_checked_staged_security_experiment_with_query_witnesses_projection[
        of A]
    by (simp add: split_def)
  show ?thesis
    using mapped unfolding projection by simp
qed

lemma
  wp_ro_absorb_checked_staged_security_experiment_with_query_witnesses_prequery_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (ro_absorb_checked_staged_security_with_query_witnesses_prequery_hit A Q)
      adversary_initial_state \<le>
    hash_relation_budget_value
      (query_index_raw_list_relation_fiber_bound Q)
      (ro_checked_staged_transcript_hash_query_budget_for budgets)"
  unfolding
    wp_ro_absorb_checked_staged_security_experiment_with_query_witnesses_prequery_eq
  by (rule
      ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_bound
        [OF wf controlled])

lemma
  ro_absorb_checked_staged_security_experiment_with_query_witnesses_outcome_projection:
  assumes outcome:
    "Some ((((data, query_start, raws, query_states), attacker_state), result),
        final_state) \<in>
      set_dist
        (execute
          (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
          initial_state)"
  shows
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (ro_absorb_checked_staged_security_experiment_with_data_state A)
          initial_state)"
proof -
  have mapped_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (ro_absorb_checked_staged_security_experiment_with_query_witnesses A \<bind>
            (\<lambda>(((data, query_start, raws, query_states), attacker_state), result).
              return ((data, attacker_state), result)))
          initial_state)"
    by (rule set_dist_bindI[OF outcome]) simp
  show ?thesis
    using mapped_support
    unfolding
      ro_absorb_checked_staged_security_experiment_with_query_witnesses_projection
    .
qed

lemma
  ro_absorb_checked_staged_security_experiment_with_query_witnesses_outcome_sync:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some ((((data, query_start, raws, query_states), attacker_state), result),
          final_state) \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
            adversary_initial_state)"
  shows
    "PState final_state = PState attacker_state \<and>
     PTranscript final_state = [] \<and>
     verifier_state_from_adversary attacker_state
       (staged_proof_transcript data) \<le> final_state \<and>
     PQueryCounter final_state = rounds"
  by (rule
      ro_absorb_checked_staged_security_experiment_with_data_state_outcome_sync
        [OF wf controlled
          ro_absorb_checked_staged_security_experiment_with_query_witnesses_outcome_projection[
            OF outcome]])

lemma
  ro_absorb_checked_staged_security_with_query_witnesses_actual_hit_imp_fresh_or_prequery:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
            adversary_initial_state)"
    and hit:
      "ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
        Q out"
  shows
    "ro_absorb_checked_staged_security_with_query_witnesses_actual_fresh_hit
        Q out \<or>
     ro_absorb_checked_staged_security_with_query_witnesses_prequery_hit
        A Q out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit_def
    by simp
next
  case (Some full)
  then obtain data query_start raws query_states attacker_state result final_state
      where out_eq:
    "out =
      Some ((((data, query_start, raws, query_states), attacker_state), result),
        final_state)"
    by (cases full) (auto split: prod.splits)
  have outcome:
    "Some ((((data, query_start, raws, query_states), attacker_state), result),
        final_state) \<in>
      set_dist
        (execute
          (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
          adversary_initial_state)"
    using support out_eq by simp
  from
    ro_absorb_checked_staged_security_experiment_with_query_witnesses_outcomeE[
      OF outcome]
  have transcript_out:
    "Some ((data, query_start, raws, query_states), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_query_witnesses A)
          adversary_initial_state)"
    by blast
  have actual:
    "length raws = rounds \<and>
     length query_states = rounds \<and>
     length (staged_query_chunks data) = rounds \<and>
     query_start \<le> attacker_state \<and>
     PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
     (\<forall>j < rounds.
       query_states ! j \<le> attacker_state \<and>
       PQueryCounter (query_states ! j) =
         PQueryCounter query_start + j \<and>
       fmlookup (HashMap attacker_state)
         (QueryIndexChallenge
           (PQueryCounter (query_states ! j))
           (PState (query_states ! j))) =
         Some (raws ! j) \<and>
       verifier_query_round_chunk
         (index (to_nat (raws ! j)))
         (staged_trace_fri_roots data)
         (staged_composition_fri_roots data)
         (staged_query_chunks data ! j)) \<and>
     (\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale)"
    by (rule
        ro_checked_staged_transcript_program_with_query_witnesses_outcome[
          OF wf controlled transcript_out])
  have query_in:
    "map (\<lambda>raw. index (to_nat raw)) raws \<in> Q"
    using hit
    unfolding out_eq
      ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit_def
    by simp
  show ?thesis
  proof (cases
      "\<forall>j < rounds.
        fmlookup (HashMap (query_states ! j))
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) = None")
    case True
    have raw_in:
      "raws \<in> query_index_raw_list_preimage Q"
      unfolding query_index_raw_list_preimage_def
      using actual query_in by blast
    have transcript_fresh:
      "ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit
        Q (Some ((data, query_start, raws, query_states), attacker_state))"
      unfolding
        ro_checked_staged_transcript_with_query_witnesses_query_index_list_fresh_hit_def
        ro_query_witnesses_query_index_list_fresh_hit_def
        ro_query_witnesses_raws_fresh_hit_def
      using raw_in actual True by auto
    show ?thesis
      unfolding out_eq
        ro_absorb_checked_staged_security_with_query_witnesses_actual_fresh_hit_def
      using transcript_fresh by simp
  next
    case False
    then obtain j where j_bound: "j < rounds"
      and lookup_not_none:
        "fmlookup (HashMap (query_states ! j))
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) \<noteq> None"
      by blast
    let ?key =
      "QueryIndexChallenge
        (PQueryCounter (query_states ! j))
        (PState (query_states ! j))"
    obtain old_raw where lookup_query_state:
      "fmlookup (HashMap (query_states ! j)) ?key = Some old_raw"
      using lookup_not_none
      by (cases "fmlookup (HashMap (query_states ! j)) ?key") auto
    have query_props:
      "\<forall>j < rounds.
        query_states ! j \<le> attacker_state \<and>
        PQueryCounter (query_states ! j) =
          PQueryCounter query_start + j \<and>
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raws ! j) \<and>
        verifier_query_round_chunk
          (index (to_nat (raws ! j)))
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)"
      using actual by blast
    have query_state_ext: "query_states ! j \<le> attacker_state"
      using query_props j_bound by blast
    have lookup_attacker:
      "fmlookup (HashMap attacker_state) ?key = Some (raws ! j)"
      using query_props j_bound by blast
    have old_raw_eq: "old_raw = raws ! j"
    proof -
      have "fmlookup (HashMap attacker_state) ?key = Some old_raw"
        by (rule hash_extension_lookup[
              OF lookup_query_state query_state_ext])
      then show ?thesis
        using lookup_attacker by simp
    qed
    have old_support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      by (rule
          ro_absorb_checked_staged_security_experiment_with_query_witnesses_outcome_projection[
            OF outcome])
    have sync:
      "PState final_state = PState attacker_state \<and>
       PTranscript final_state = [] \<and>
       verifier_state_from_adversary attacker_state
         (staged_proof_transcript data) \<le> final_state \<and>
       PQueryCounter final_state = rounds"
      by (rule
          ro_absorb_checked_staged_security_experiment_with_query_witnesses_outcome_sync[
            OF wf controlled outcome])
    have rel:
      "ro_absorb_checked_query_index_list_relation A Q ?key (raws ! j)"
      unfolding ro_absorb_checked_query_index_list_relation_def
      by (intro exI[
            of _ "Some (((data, attacker_state), result), final_state)"]
          exI[of _ data] exI[of _ attacker_state]
          exI[of _ result] exI[of _ final_state]
          exI[of _ query_start] exI[of _ raws]
          exI[of _ "map (\<lambda>raw. index (to_nat raw)) raws"]
          exI[of _ query_states] exI[of _ j] conjI)
        (use old_support actual query_in j_bound query_props sync in auto)
    have initial_none:
      "fmlookup (HashMap adversary_initial_state) ?key = None"
      by (simp add: adversary_initial_state_def)
    have rel_hit:
      "hash_relation_hit
        (ro_absorb_checked_query_index_list_relation A Q)
        adversary_initial_state attacker_state"
      unfolding hash_relation_hit_def
      by (intro exI[of _ ?key] exI[of _ "raws ! j"] conjI)
        (use initial_none lookup_attacker rel in simp_all)
    show ?thesis
      unfolding out_eq
        ro_absorb_checked_staged_security_with_query_witnesses_prequery_hit_def
        ro_absorb_checked_staged_security_with_data_state_query_index_list_prequery_hit_def
      using rel_hit by simp
  qed
qed

lemma
  ro_absorb_checked_staged_security_with_query_witnesses_actual_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
        Q)
      adversary_initial_state \<le>
    nnreal (card (query_index_raw_list_preimage Q)) *
        (1 / nnreal size) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (ro_checked_staged_transcript_hash_query_budget_for budgets)"
proof -
  have split:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
        Q)
      adversary_initial_state \<le>
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (\<lambda>out.
        ro_absorb_checked_staged_security_with_query_witnesses_actual_fresh_hit
          Q out \<or>
        ro_absorb_checked_staged_security_with_query_witnesses_prequery_hit
          A Q out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
            adversary_initial_state)"
      and hit:
        "ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
          Q out"
    show
      "ro_absorb_checked_staged_security_with_query_witnesses_actual_fresh_hit
          Q out \<or>
       ro_absorb_checked_staged_security_with_query_witnesses_prequery_hit
          A Q out"
      by (rule
          ro_absorb_checked_staged_security_with_query_witnesses_actual_hit_imp_fresh_or_prequery[
            OF wf controlled support hit])
  qed
  also have "... \<le>
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (ro_absorb_checked_staged_security_with_query_witnesses_actual_fresh_hit
        Q)
      adversary_initial_state +
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (ro_absorb_checked_staged_security_with_query_witnesses_prequery_hit
        A Q)
      adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
    nnreal (card (query_index_raw_list_preimage Q)) *
        (1 / nnreal size) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (ro_checked_staged_transcript_hash_query_budget_for budgets)"
    by (rule add_mono)
      (rule
         wp_ro_absorb_checked_staged_security_experiment_with_query_witnesses_actual_fresh_bound,
       rule
         wp_ro_absorb_checked_staged_security_experiment_with_query_witnesses_prequery_bound[
           OF wf controlled])
  finally show ?thesis .
qed

lemma
  ro_absorb_checked_staged_security_experiment_with_query_witnesses_acceptance_le_actual_space_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      accepted adversary_initial_state \<le>
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
        fri_query_index_list_space)
      adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
    "out \<in>
      set_dist
        (execute
          (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
          adversary_initial_state)"
    and accepted: "accepted out"
  from accepted obtain full where out_eq: "out = Some full"
    unfolding accepted_def by (cases out) auto
  obtain data query_start raws query_states attacker_state result final_state
      where full_eq:
    "full =
      ((((data, query_start, raws, query_states), attacker_state), result),
        final_state)"
    by (cases full) (auto split: prod.splits)
  have outcome:
    "Some ((((data, query_start, raws, query_states), attacker_state), result),
        final_state) \<in>
      set_dist
        (execute
          (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
          adversary_initial_state)"
    using support out_eq full_eq by simp
  from
    ro_absorb_checked_staged_security_experiment_with_query_witnesses_outcomeE[
      OF outcome]
  have transcript_out:
    "Some ((data, query_start, raws, query_states), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_query_witnesses A)
          adversary_initial_state)"
    by blast
  have actual:
    "length raws = rounds \<and>
     (\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale)"
    using
      ro_checked_staged_transcript_program_with_query_witnesses_outcome[
        OF wf controlled transcript_out]
    by blast
  have list_len:
    "length (map (\<lambda>raw. index (to_nat raw)) raws) = rounds"
    using actual by simp
  have list_space:
    "map (\<lambda>raw. index (to_nat raw)) raws \<in> fri_query_index_list_space"
    unfolding fri_query_index_list_space_def query_sample_space_def
    using list_len index_less_query_sample_space by auto
  show
    "ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit
      fri_query_index_list_space out"
    unfolding out_eq full_eq
      ro_absorb_checked_staged_security_with_query_witnesses_actual_query_index_list_hit_def
    using list_space by simp
qed

lemma
  wp_ro_absorb_checked_staged_security_experiment_with_query_witnesses_acceptance_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      accepted adversary_initial_state \<le>
    nnreal
        (card
          (query_index_raw_list_preimage fri_query_index_list_space)) *
        (1 / nnreal size) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          fri_query_index_list_space)
        (ro_checked_staged_transcript_hash_query_budget_for budgets)"
  by (rule order_trans[
        OF
          ro_absorb_checked_staged_security_experiment_with_query_witnesses_acceptance_le_actual_space_hit[
            OF wf controlled]
          ro_absorb_checked_staged_security_with_query_witnesses_actual_hit_bound[
            OF wf controlled]])

lemma
  ro_absorb_checked_staged_security_experiment_with_query_witnesses_acceptance_eq_data_state:
  "wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      accepted s =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_data_state A)
      accepted s"
proof -
  let ?project =
    "\<lambda>(((data, query_start, raws, query_states), attacker_state), result).
      ((data, attacker_state), result)"
  have event_map:
    "(\<lambda>out. case out of
      None \<Rightarrow> accepted None
    | Some (x, t) \<Rightarrow> accepted (Some (?project x, t))) = accepted"
    unfolding accepted_def
    by (rule ext) (auto split: option.splits prod.splits)
  have mapped:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A \<bind>
        (\<lambda>x. return (?project x)))
      accepted s =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      accepted s"
    by (subst wp_event_bind_return_map) (simp only: event_map)
  have projection:
    "ro_absorb_checked_staged_security_experiment_with_query_witnesses A \<bind>
        (\<lambda>x. return (?project x)) =
      ro_absorb_checked_staged_security_experiment_with_data_state A"
    using
      ro_absorb_checked_staged_security_experiment_with_query_witnesses_projection[
        of A]
    by (simp add: split_def)
  show ?thesis
    using mapped unfolding projection by simp
qed

lemma
  ro_absorb_checked_staged_security_experiment_data_state_acceptance_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_data_state A)
      accepted adversary_initial_state \<le>
    nnreal
        (card
          (query_index_raw_list_preimage fri_query_index_list_space)) *
        (1 / nnreal size) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          fri_query_index_list_space)
        (ro_checked_staged_transcript_hash_query_budget_for budgets)"
  unfolding
    ro_absorb_checked_staged_security_experiment_with_query_witnesses_acceptance_eq_data_state[
      symmetric]
  by (rule
      wp_ro_absorb_checked_staged_security_experiment_with_query_witnesses_acceptance_bound[
        OF wf controlled])

end

end
