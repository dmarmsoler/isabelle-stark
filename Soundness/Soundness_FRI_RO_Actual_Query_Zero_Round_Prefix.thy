(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Zero_Round_Prefix.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Zero_Round_Prefix
  imports
    Soundness_FRI_RO_Actual_Query_Joint_Evidence
    Soundness_FRI_Zero_Round_Target
begin

text \<open>
  Zero-round proof layer for the root-prefix ghost experiment.  When the trace
  FRI has no fold round, the saved commitment is the initial trace root after
  its domain-separated transcript absorption.  No protocol transition is
  changed.
\<close>

context soundness
begin

lemma ro_checked_staged_after_first_trace_fri_root_prefix_program_zero_facts:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              (fr, trace_bs, first_root))
            s)"
  shows "s \<le> t \<and> PQueryCounter t = PQueryCounter s"
proof -
  from outcome obtain trace_final s1 s2 as s3 dg s4 s5 s6
      composition_roots composition_bs s7 composition_final s8 s9 where
    trace_final_out:
      "Some (trace_final, s1) \<in>
        set_dist (execute (trace_final_stage A []) s)"
    and trace_final_record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message trace_final) s1)"
    and alpha_out:
      "Some (as, s3) \<in>
        set_dist (execute (ro_staged_alpha_program (length spec)) s2)"
    and degree_out:
      "Some (dg, s4) \<in> set_dist (execute (degree_stage A as) s3)"
    and degree_record_out:
      "Some ((), s5) \<in>
        set_dist (execute (ro_record_staged_message dg) s4)"
    and assert_out:
      "Some ((), s6) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))
            s5)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s7) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])
            s6)"
    and composition_final_out:
      "Some (composition_final, s8) \<in>
        set_dist
          (execute
            (composition_final_stage A dg composition_bs)
            s7)"
    and composition_final_record_out:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (ro_record_staged_message composition_final)
            s8)"
    and t_eq: "t = s9"
    using outcome
    unfolding
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def
      zero
    by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)
  have trace_final_controlled:
      "controlled_ro_program (trace_final_budget budgets)
        (trace_final_stage A [])"
    using controlled
    unfolding staged_adversary_controlled_def
    by blast
  have trace_final_ext: "s \<le> s1"
    using controlled_ro_program_extension[
      OF trace_final_controlled] trace_final_out
    unfolding hash_extension_preserving_def
    by blast
  have trace_final_counter: "PQueryCounter s1 = PQueryCounter s"
    using controlled_stage_outcome_fields[
      OF trace_final_controlled trace_final_out]
    by simp
  have trace_record_ext: "s1 \<le> s2"
    using ro_record_staged_message_absorb_lookup_state[
      OF trace_final_record_out]
    by blast
  have trace_record_counter: "PQueryCounter s2 = PQueryCounter s1"
    using ro_record_staged_message_hash_extends_query_counter[
      OF trace_final_record_out]
    by simp
  have alpha_props:
      "ro_absorb_lookup_chain s3 (PState s2) as (PState s3) \<and> s2 \<le> s3"
    by (rule ro_staged_alpha_program_absorb_lookup_chain[OF alpha_out])
  have alpha_counter: "PQueryCounter s3 = PQueryCounter s2"
    by (rule ro_staged_alpha_program_query_counter[OF alpha_out])
  have degree_controlled:
      "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled
    unfolding staged_adversary_controlled_def
    by blast
  have degree_ext: "s3 \<le> s4"
    using controlled_ro_program_extension[OF degree_controlled] degree_out
    unfolding hash_extension_preserving_def
    by blast
  have degree_counter: "PQueryCounter s4 = PQueryCounter s3"
    using controlled_stage_outcome_fields[OF degree_controlled degree_out]
    by simp
  have degree_record_ext: "s4 \<le> s5"
    using ro_record_staged_message_absorb_lookup_state[
      OF degree_record_out]
    by blast
  have degree_record_counter: "PQueryCounter s5 = PQueryCounter s4"
    using ro_record_staged_message_hash_extends_query_counter[
      OF degree_record_out]
    by simp
  have s6_eq: "s6 = s5"
    using assert_out
    unfolding assert_def
    by (cases
      "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_bound:
      "0 + ceil_log (to_nat dg + 1) \<le>
        length (composition_fri_budgets budgets)"
    using assert_out wf
    unfolding assert_def staged_budget_wellformed_def
    by (cases
      "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_props:
      "ro_absorb_lookup_chain s7 (PState s6) composition_roots
          (PState s7) \<and>
        s6 \<le> s7"
    by (rule ro_staged_composition_fri_program_absorb_lookup_chain[
      OF controlled composition_bound composition_out])
  have composition_counter: "PQueryCounter s7 = PQueryCounter s6"
    by (rule ro_staged_composition_fri_program_query_counter[
      OF controlled composition_bound composition_out])
  have composition_final_controlled:
      "controlled_ro_program (composition_final_budget budgets)
        (composition_final_stage A dg composition_bs)"
    using controlled
    unfolding staged_adversary_controlled_def
    by blast
  have composition_final_ext: "s7 \<le> s8"
    using controlled_ro_program_extension[
      OF composition_final_controlled] composition_final_out
    unfolding hash_extension_preserving_def
    by blast
  have composition_final_counter: "PQueryCounter s8 = PQueryCounter s7"
    using controlled_stage_outcome_fields[
      OF composition_final_controlled composition_final_out]
    by simp
  have composition_record_ext: "s8 \<le> s9"
    using ro_record_staged_message_absorb_lookup_state[
      OF composition_final_record_out]
    by blast
  have composition_record_counter: "PQueryCounter s9 = PQueryCounter s8"
    using ro_record_staged_message_hash_extends_query_counter[
      OF composition_final_record_out]
    by simp
  have ext: "s \<le> s9"
    using trace_final_ext trace_record_ext conjunct2[OF alpha_props]
      degree_ext degree_record_ext s6_eq conjunct2[OF composition_props]
      composition_final_ext composition_record_ext
    by (metis hash_ext_trans)
  have counter: "PQueryCounter s9 = PQueryCounter s"
    using trace_final_counter trace_record_counter alpha_counter
      degree_counter degree_record_counter s6_eq composition_counter
      composition_final_counter composition_record_counter
    by simp
  show ?thesis
    using ext counter t_eq by simp
qed

lemma ro_checked_staged_transcript_program_with_first_root_zero_fields:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
  shows
    "\<exists>fr.
      prefix = (fr, [], fr) \<and>
      staged_trace_root data = fr \<and>
      staged_trace_fri_roots data = [] \<and>
      staged_trace_fri_challenges data = [] \<and>
      prefix_state \<le> query_start \<and>
      query_start \<le> attacker_state \<and>
      PQueryCounter query_start = 0"
proof -
  from ro_checked_staged_transcript_program_with_first_root_outcomeE[
      OF outcome]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
    and after_out:
      "Some (head_data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              prefix)
            prefix_final)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    by blast
  obtain fr trace_bs first_root where prefix_eq:
      "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  have prefix_props:
      "trace_bs = [] \<and> first_root = fr \<and>
       prefix_state = prefix_final \<and>
       adversary_initial_state \<le> prefix_final \<and>
       ro_absorb_lookup_chain prefix_final
         (PState adversary_initial_state) [fr] (PState prefix_final) \<and>
       PQueryCounter prefix_final = PQueryCounter adversary_initial_state"
    by (rule ro_staged_first_trace_fri_root_prefix_program_zero_chain[
          OF controlled zero])
      (use prefix_out prefix_eq in simp)
  have after_fields:
      "staged_trace_root head_data = fr \<and>
       staged_trace_fri_roots head_data = [] \<and>
       staged_trace_fri_challenges head_data = []"
    by (rule
      ro_checked_staged_after_first_trace_fri_root_prefix_program_zero_fields[
        OF zero])
      (use after_out prefix_eq in simp)
  have after_facts:
      "prefix_final \<le> query_start \<and>
       PQueryCounter query_start = PQueryCounter prefix_final"
    by (rule
      ro_checked_staged_after_first_trace_fri_root_prefix_program_zero_facts[
        OF zero wf controlled])
      (use after_out prefix_eq in simp)
  have query_props:
      "query_start \<le> attacker_state"
    using
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
        OF wf controlled outcome]
    by blast
  show ?thesis
    using prefix_eq prefix_props after_fields after_facts query_props data_eq
    by (intro exI[of _ fr]) (simp add: adversary_initial_state_def)
qed

lemma ro_verifier_query_round_program_authenticated_trace_openings_zero:
  fixes s t :: "'f protocol_channel"
  assumes f_fl_zero: "f_fl = []"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (ro_verifier_query_round_program
              fr f_fl f_final as fl final) s)"
  obtains raw idx fv trace_openings where
    "idx = index (to_nat raw)"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    "length trace_openings = length (powers_scaled idx)"
    "map opening_value trace_openings = fv"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "opening_value (trace_openings ! 0) = f_final"
proof -
  from outcome obtain raw s1 fv s2 f_i f_x f_len f_pow s3 s4
      i x len pw s5 where
    challenge:
      "Some (raw, s1) \<in> set_dist (execute receive_query_index_challenge s)"
    and decommit:
      "Some (fv, s2) \<in>
        set_dist
          (execute
            (mmap (ro_check_decommit_on_query fr (index (to_nat raw)))) s1)"
    and trace_fri:
      "Some ((f_i, f_x, f_len, f_pow), s3) \<in>
        set_dist
          (execute
            (mfold (index (to_nat raw), hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl)) s2)"
    and trace_assert:
      "Some ((), s4) \<in> set_dist (execute (assert (f_x = f_final)) s3)"
    and composition_fri:
      "Some ((i, x, len, pw), s5) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat raw),
                cp_eval as fv (h ^ index (to_nat raw) * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl)) s4)"
    and composition_assert:
      "Some ((), t) \<in> set_dist (execute (assert (x = final)) s5)"
    unfolding ro_verifier_query_round_program_def
    by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)
  let ?idx = "index (to_nat raw)"
  have idx_sample: "?idx \<in> query_sample_space"
    using index_less_query_sample_space
    unfolding query_sample_space_def by simp
  from ro_check_decommit_on_query_authenticated_openings[
      OF idx_sample decommit]
  obtain trace_openings where
    trace_len:
      "length trace_openings = length (powers_scaled ?idx)"
    and trace_values: "map opening_value trace_openings = fv"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled ?idx"
    and trace_table_s2:
      "partial_authenticated_table fr (scale * clength) trace_openings s2"
    by blast
  have s2_s3: "s2 \<le> s3"
    using ro_receive_query_commits_outcome_extends_counter[OF trace_fri]
    by blast
  have trace_value: "f_x = hd fv"
    using trace_fri f_fl_zero
    unfolding ro_receive_query_commits_def
    by simp
  have trace_assert_props: "f_x = f_final \<and> s4 = s3"
    using trace_assert unfolding assert_def
    by (cases "f_x = f_final") (auto simp: throw_no_outcome)
  have s4_s5: "s4 \<le> s5"
    using ro_receive_query_commits_outcome_extends_counter[OF composition_fri]
    by blast
  have t_eq: "t = s5"
    using composition_assert unfolding assert_def
    by (cases "x = final") (auto simp: throw_no_outcome)
  have s2_t: "s2 \<le> t"
    using s2_s3 s4_s5 trace_assert_props t_eq
    by (meson hash_ext_trans)
  have trace_table_t:
      "partial_authenticated_table fr (scale * clength) trace_openings t"
    by (rule partial_authenticated_table_mono[OF trace_table_s2 s2_t])
  have trace_nonempty: "trace_openings \<noteq> []"
  proof
    assume "trace_openings = []"
    then have "length trace_openings = 0"
      by simp
    then show False
      using trace_len powers_pos
      unfolding powers_scaled_def by simp
  qed
  have trace_first:
      "opening_value (trace_openings ! 0) = hd fv"
    using trace_values trace_nonempty
    by (cases trace_openings) auto
  have trace_final:
      "opening_value (trace_openings ! 0) = f_final"
    using trace_first trace_value trace_assert_props by simp
  have challenge_lookup_s1:
      "fmlookup (HashMap s1)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF challenge] by simp
  have s1_s2: "s1 \<le> s2"
    using ro_check_decommit_on_query_outcome_with_lookup_chain[OF decommit]
    by blast
  have s1_t: "s1 \<le> t"
    by (rule hash_ext_trans[OF s1_s2 s2_t])
  have lookup_t:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF challenge_lookup_s1 s1_t])
  show ?thesis
    by (rule that[of ?idx raw trace_openings fv])
      (use lookup_t trace_len trace_values trace_indices trace_table_t
        trace_final in simp_all)
qed

lemma ro_absorb_checked_staged_zero_round_actual_query_boundary_syncE:
  fixes final_state :: "'f protocol_channel"
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and builder_out:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and verifier_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and clean: "\<not> hash_map_output_collision final_state"
  obtains head_data query_chunks f_fl fl verifier_query_state
      fr f_final as final where
    "Some ((raws, query_states, query_chunks), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program_with_witnesses A
            (staged_trace_fri_roots head_data)
            (staged_composition_fri_roots head_data)
            query_start 0 rounds)
          query_start)"
    "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    "fr = staged_trace_root data"
    "map fst f_fl = staged_trace_fri_challenges data"
    "map snd f_fl = staged_trace_fri_roots data"
    "f_final = staged_trace_final data"
    "as = staged_alphas data"
    "map fst fl = staged_composition_fri_challenges data"
    "map snd fl = staged_composition_fri_roots data"
    "final = staged_composition_final data"
    "f_fl = []"
    "to_nat (staged_degree data) \<le> maxDegree"
    "Some (results, final_state) \<in>
      set_dist
        (execute
          (ntimes
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          verifier_query_state)"
    "prefix_state \<le> query_start"
    "query_start \<le> attacker_state"
    "attacker_state \<le> verifier_query_state"
    "PState verifier_query_state = PState query_start"
    "PQueryCounter verifier_query_state = PQueryCounter query_start"
    "PQueryCounter query_start = 0"
    "PTranscript verifier_query_state = List.concat query_chunks @ []"
    "length raws = rounds"
    "length query_chunks = rounds"
    "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
proof -
  from ro_checked_staged_transcript_program_with_first_root_outcomeE[
      OF builder_out]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
    and after_out:
      "Some (head_data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              prefix)
            prefix_final)"
    and query_out:
      "Some ((raws, query_states, query_chunks), attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots head_data)
              (staged_composition_fri_roots head_data)
              query_start 0 rounds)
            query_start)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    by blast

  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
        ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
          OF builder_out])
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength \<and>
       length (staged_alphas data) = length spec \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       length (staged_composition_fri_challenges data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       ceil_log (to_nat (staged_degree data) + 1) \<le>
         ceil_log (maxDegree + 1) \<and>
       length (staged_query_chunks data) = rounds"
    by (rule ro_checked_staged_transcript_program_outcome_shape[
          OF original_out])
  have query_bound:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_props:
      "length raws = rounds \<and>
       length query_states = rounds \<and>
       length query_chunks = rounds \<and>
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
         verifier_query_round_chunk (index (to_nat (raws ! j)))
           (staged_trace_fri_roots head_data)
           (staged_composition_fri_roots head_data)
           (query_chunks ! j)) \<and>
       (\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale)"
    by (rule ro_checked_staged_query_program_with_witnesses_outcome[
          OF controlled query_bound query_out])

  have boundary_trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    using shape by simp
  have boundary_composition_len:
      "length (staged_composition_fri_roots data) =
        ceil_log (to_nat (staged_degree data) + 1)"
    using shape by simp
  have boundary_alphas_len:
      "length (staged_alphas data) = length spec"
    using shape by simp
  have boundary_query_idxs_len:
      "length (map (\<lambda>raw. index (to_nat raw)) raws) = rounds"
    using query_props by simp
  have boundary_chunks_len:
      "length (staged_query_chunks data) = rounds"
    using shape by simp
  have boundary_chunk_shapes:
      "\<forall>j < rounds.
        verifier_query_round_chunk
          (map (\<lambda>raw. index (to_nat raw)) raws ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)"
    using query_props data_eq by simp

  have full_sync:
      "(PState final_state = PState attacker_state \<and>
        PTranscript final_state = [] \<and>
        verifier_state_from_adversary attacker_state
          (staged_proof_transcript data) \<le> final_state \<and>
        PQueryCounter final_state = rounds) \<and>
       (\<exists>fr trace_pairs f_final as dg composition_pairs final
            verifier_query_state.
          fr = staged_trace_root data \<and>
          map fst trace_pairs = staged_trace_fri_challenges data \<and>
          map snd trace_pairs = staged_trace_fri_roots data \<and>
          f_final = staged_trace_final data \<and>
          as = staged_alphas data \<and>
          dg = staged_degree data \<and>
          to_nat dg \<le> maxDegree \<and>
          map fst composition_pairs =
            staged_composition_fri_challenges data \<and>
          map snd composition_pairs =
            staged_composition_fri_roots data \<and>
          final = staged_composition_final data \<and>
          Some (results, final_state) \<in>
            set_dist
              (execute
                (ntimes
                  (ro_verifier_query_round_program fr trace_pairs f_final as
                    composition_pairs final)
                  rounds)
                verifier_query_state) \<and>
          attacker_state \<le> verifier_query_state \<and>
          PTranscript verifier_query_state =
            List.concat (staged_query_chunks data) \<and>
          PQueryCounter verifier_query_state = 0)"
    by (rule
        ro_checked_staged_transcript_program_ro_verify_monad_full_sync[
          OF wf controlled original_out verifier_out])
  then obtain fr f_fl f_final as dg fl final verifier_query_state where
    fr_eq: "fr = staged_trace_root data"
    and trace_challenges_eq:
      "map fst f_fl = staged_trace_fri_challenges data"
    and trace_roots_eq:
      "map snd f_fl = staged_trace_fri_roots data"
    and trace_final_eq: "f_final = staged_trace_final data"
    and alphas_eq: "as = staged_alphas data"
    and degree_eq: "dg = staged_degree data"
    and degree_bound_raw: "to_nat dg \<le> maxDegree"
    and composition_challenges_eq:
      "map fst fl = staged_composition_fri_challenges data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and composition_final_eq: "final = staged_composition_final data"
    and verifier_query_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            verifier_query_state)"
    and attacker_verifier_ext:
      "attacker_state \<le> verifier_query_state"
    and verifier_transcript:
      "PTranscript verifier_query_state =
        List.concat (staged_query_chunks data)"
    and verifier_counter: "PQueryCounter verifier_query_state = 0"
    by blast
  have f_fl_zero: "f_fl = []"
    using trace_roots_eq boundary_trace_len zero by auto
  have degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    using degree_eq degree_bound_raw by simp
  have verifier_query_props:
      "PTranscript final_state = [] \<and>
       ro_absorb_lookup_chain final_state (PState verifier_query_state)
         (List.concat (staged_query_chunks data)) (PState final_state) \<and>
       verifier_query_state \<le> final_state \<and>
       PQueryCounter final_state =
         PQueryCounter verifier_query_state + rounds"
    by (rule
        ntimes_ro_verifier_query_round_program_aligns_expected_chunks[
          OF boundary_chunks_len boundary_query_idxs_len
            boundary_chunk_shapes _ _ _ verifier_query_out])
      (use verifier_transcript trace_roots_eq composition_roots_eq in simp_all)
  have verifier_chain:
      "ro_absorb_lookup_chain final_state (PState verifier_query_state)
        (List.concat (staged_query_chunks data)) (PState final_state)"
    using verifier_query_props by simp
  have verifier_ext: "verifier_query_state \<le> final_state"
    using verifier_query_props by simp

  have attacker_final_ext: "attacker_state \<le> final_state"
    by (rule hash_ext_trans[OF attacker_verifier_ext verifier_ext])
  have builder_chain_attacker:
      "ro_absorb_lookup_chain attacker_state (PState query_start)
        (List.concat query_chunks) (PState attacker_state)"
    using ro_checked_staged_query_program_with_witnesses_absorb_lookup_chain[
      OF controlled query_bound query_out]
    by blast
  have builder_chain_final:
      "ro_absorb_lookup_chain final_state (PState query_start)
        (List.concat query_chunks) (PState attacker_state)"
    by (rule ro_absorb_lookup_chain_mono[
          OF builder_chain_attacker attacker_final_ext])

  have sync:
      "PState final_state = PState attacker_state \<and>
       PTranscript final_state = [] \<and>
       verifier_state_from_adversary attacker_state
         (staged_proof_transcript data) \<le> final_state \<and>
       PQueryCounter final_state = rounds"
    by (rule ro_checked_staged_transcript_program_ro_verify_monad_sync[
          OF wf controlled original_out verifier_out])
  have builder_chain_final':
      "ro_absorb_lookup_chain final_state (PState query_start)
        (List.concat (staged_query_chunks data)) (PState final_state)"
    using builder_chain_final sync data_eq by simp
  have verifier_builder_state:
      "PState verifier_query_state = PState query_start"
    by (rule ro_absorb_lookup_chain_start_functional_if_clean[
          OF clean verifier_chain builder_chain_final'])

  from ro_checked_staged_transcript_program_with_first_root_zero_fields[
      OF zero wf controlled builder_out]
  obtain prefix_fr where zero_fields:
      "prefix = (prefix_fr, [], prefix_fr) \<and>
       staged_trace_root data = prefix_fr \<and>
       staged_trace_fri_roots data = [] \<and>
       staged_trace_fri_challenges data = [] \<and>
       prefix_state \<le> query_start \<and>
       query_start \<le> attacker_state \<and>
       PQueryCounter query_start = 0"
    by blast
  have counter_eq:
      "PQueryCounter verifier_query_state = PQueryCounter query_start"
    using verifier_counter zero_fields by simp
  have verifier_transcript':
      "PTranscript verifier_query_state = List.concat query_chunks @ []"
    using verifier_transcript data_eq by simp

  show ?thesis
    by (rule that[OF query_out data_eq fr_eq trace_challenges_eq
          trace_roots_eq trace_final_eq alphas_eq
          composition_challenges_eq composition_roots_eq
          composition_final_eq f_fl_zero degree_bound verifier_query_out])
      (use zero_fields query_props attacker_verifier_ext verifier_builder_state
        counter_eq verifier_transcript' in simp_all)
qed

lemma
  ro_checked_staged_query_program_with_witnesses_verifier_authenticated_trace_openings_zero:
  fixes builder sent verifier_state verifier_final :: "'f protocol_channel"
    and rest :: "'f list"
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and builder_out:
      "Some ((raws, query_states, chunks), sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots builder i n)
            builder)"
    and sent_ext: "sent \<le> verifier_state"
    and state_eq: "PState verifier_state = PState builder"
    and counter_eq: "PQueryCounter verifier_state = PQueryCounter builder"
    and transcript_prefix:
      "PTranscript verifier_state = List.concat chunks @ rest"
    and f_fl_zero: "f_fl = []"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and verifier_out:
      "Some (results, verifier_final) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program fr f_fl f_final as fl final)
              n)
            verifier_state)"
  shows
    "\<exists>trace_openings_at.
      verifier_state \<le> verifier_final \<and>
      length raws = n \<and>
      length query_states = n \<and>
      length chunks = n \<and>
      (\<forall>j < n.
        map opening_index (trace_openings_at j) =
          powers_scaled (index (to_nat (raws ! j))) \<and>
        partial_authenticated_table fr (scale * clength)
          (trace_openings_at j) verifier_final \<and>
        opening_value (trace_openings_at j ! 0) = f_final)"
  using bound builder_out sent_ext state_eq counter_eq transcript_prefix
    verifier_out
proof (induction n arbitrary: i builder sent verifier_state verifier_final
    raws query_states chunks results)
  case 0
  then show ?case
    by (intro exI[of _ "\<lambda>_. []"]) (auto intro: hash_ext_refl)
next
  case (Suc n)
  let ?round =
    "ro_verifier_query_round_program fr f_fl f_final as fl final"
  from Suc.prems(2)
  obtain witness_raw witness_chunk raws_tail query_states_tail chunks_tail
      ws1 ws2 ws_assert ws3 where
    witness_challenge:
      "Some (witness_raw, ws1) \<in>
        set_dist (execute receive_query_index_challenge builder)"
    and witness_stage:
      "Some (witness_chunk, ws2) \<in>
        set_dist (execute (query_opening_stage A i witness_raw) ws1)"
    and witness_assert:
      "Some ((), ws_assert) \<in>
        set_dist
          (execute
            (assert
              (verifier_query_round_chunk (index (to_nat witness_raw))
                trace_roots composition_roots witness_chunk))
            ws2)"
    and witness_record:
      "Some ((), ws3) \<in>
        set_dist (execute (ro_record_staged_messages witness_chunk) ws_assert)"
    and witness_tail:
      "Some ((raws_tail, query_states_tail, chunks_tail), sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots ws3 (Suc i) n)
            ws3)"
    and raws_eq: "raws = witness_raw # raws_tail"
    and query_states_eq: "query_states = builder # query_states_tail"
    and chunks_eq: "chunks = witness_chunk # chunks_tail"
    unfolding ro_checked_staged_query_program_with_witnesses.simps Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have witness_assert_props:
      "ws_assert = ws2 \<and>
       verifier_query_round_chunk (index (to_nat witness_raw))
         trace_roots composition_roots witness_chunk"
    using witness_assert
    unfolding assert_def
    by (cases
        "verifier_query_round_chunk (index (to_nat witness_raw))
          trace_roots composition_roots witness_chunk")
      (simp_all add: throw_no_outcome)
  have ws_assert_eq: "ws_assert = ws2"
    using witness_assert_props by simp
  have witness_record':
      "Some ((), ws3) \<in>
        set_dist (execute (ro_record_staged_messages witness_chunk) ws2)"
    using witness_record ws_assert_eq by simp

  from Suc.prems(7)
  obtain verifier_mid results_tail where
    verifier_head:
      "Some ((), verifier_mid) \<in>
        set_dist (execute ?round verifier_state)"
    and verifier_tail:
      "Some (results_tail, verifier_final) \<in>
        set_dist (execute (ntimes ?round n) verifier_mid)"
    and results_eq: "results = () # results_tail"
    by (auto elim!: set_dist_bindE)

  have ordinary:
      "Some (chunks, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots
              composition_roots i (Suc n))
            builder)"
    by (rule
        ro_checked_staged_query_program_with_witnesses_projection_outcome[
          OF Suc.prems(2)])

  from ro_checked_staged_query_program_Suc_verifier_round_sync_lookupE[
      where budgets=budgets and A=A and i=i and n=n
        and builder=builder and sent=sent
        and verifier_state=verifier_state and verifier_state'=verifier_mid
        and chunks=chunks and rest=rest
        and trace_roots=trace_roots and composition_roots=composition_roots
        and f_fl=f_fl and fl=fl and fr=fr and f_final=f_final
        and as=as and final=final,
      OF controlled Suc.prems(1) ordinary Suc.prems(3) Suc.prems(4)
        Suc.prems(5) Suc.prems(6) trace_roots_eq composition_roots_eq
        verifier_head]
  obtain sync_raw sync_chunk sync_chunks ss1 ss2 ss3 where
    sync_challenge:
      "Some (sync_raw, ss1) \<in>
        set_dist (execute receive_query_index_challenge builder)"
    and sync_stage:
      "Some (sync_chunk, ss2) \<in>
        set_dist (execute (query_opening_stage A i sync_raw) ss1)"
    and sync_chunk_shape:
      "verifier_query_round_chunk (index (to_nat sync_raw))
        trace_roots composition_roots sync_chunk"
    and sync_record:
      "Some ((), ss3) \<in>
        set_dist (execute (ro_record_staged_messages sync_chunk) ss2)"
    and sync_tail:
      "Some (sync_chunks, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n)
            ss3)"
    and sync_chunks_eq: "chunks = sync_chunk # sync_chunks"
    and state_mid_sync: "PState verifier_mid = PState ss3"
    and transcript_mid:
      "PTranscript verifier_mid = List.concat sync_chunks @ rest"
    and verifier_step_ext: "verifier_state \<le> verifier_mid"
    and counter_mid:
      "PQueryCounter verifier_mid = Suc (PQueryCounter builder)"
    and sync_head_chain:
      "ro_absorb_lookup_chain sent (PState builder) sync_chunk (PState ss3)"
    and sync_recorded:
      "fmlookup (HashMap sent)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some sync_raw"
    .

  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have tail_bound:
      "Suc i + n \<le> length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have witness_stage_controlled:
      "controlled_ro_program (query_opening_budgets budgets ! i)
        (query_opening_stage A i witness_raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have witness_challenge_props:
      "builder \<le> ws1 \<and>
       PState ws1 = PState builder \<and>
       PTranscript ws1 = PTranscript builder \<and>
       fmlookup (HashMap ws1)
         (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
         Some witness_raw"
    by (rule receive_query_index_challenge_outcome[OF witness_challenge])
  have witness_challenge_state: "PState ws1 = PState builder"
    using witness_challenge_props by simp
  have witness_stage_ext: "ws1 \<le> ws2"
    using controlled_ro_program_extension[OF witness_stage_controlled]
      witness_stage
    unfolding hash_extension_preserving_def by blast
  have witness_stage_state: "PState ws2 = PState ws1"
    using controlled_stage_outcome_fields[
      OF witness_stage_controlled witness_stage]
    by simp
  have witness_record_chain:
      "ro_absorb_lookup_chain ws3 (PState ws2) witness_chunk (PState ws3) \<and>
       ws2 \<le> ws3"
    by (rule ro_record_staged_messages_absorb_lookup_chain[
          OF witness_record'])
  have witness_tail_ordinary:
      "Some (chunks_tail, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n)
            ws3)"
    by (rule
        ro_checked_staged_query_program_with_witnesses_projection_outcome[
          OF witness_tail])
  have witness_tail_ext: "ws3 \<le> sent"
    using ro_checked_staged_query_program_absorb_lookup_chain[
      OF controlled tail_bound witness_tail_ordinary]
    by simp
  have ws1_sent: "ws1 \<le> sent"
    by (rule hash_ext_trans[OF witness_stage_ext])
      (rule hash_ext_trans[
        OF conjunct2[OF witness_record_chain] witness_tail_ext])
  have witness_recorded:
      "fmlookup (HashMap sent)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some witness_raw"
    by (rule hash_extension_lookup)
      (use witness_challenge_props ws1_sent in simp_all)
  have sync_raw_eq: "sync_raw = witness_raw"
    using sync_recorded witness_recorded by simp
  have sync_chunk_eq: "sync_chunk = witness_chunk"
    and sync_chunks_tail_eq: "sync_chunks = chunks_tail"
    using sync_chunks_eq chunks_eq by simp_all

  have witness_head_chain:
      "ro_absorb_lookup_chain sent (PState builder) witness_chunk (PState ws3)"
  proof -
    have chain:
        "ro_absorb_lookup_chain sent (PState ws2) witness_chunk (PState ws3)"
      by (rule ro_absorb_lookup_chain_mono[
            OF conjunct1[OF witness_record_chain] witness_tail_ext])
    show ?thesis
      using chain witness_challenge_state witness_stage_state by simp
  qed
  have head_state_eq: "PState ss3 = PState ws3"
  proof -
    have sync_chain:
        "ro_absorb_lookup_chain sent (PState builder) witness_chunk (PState ss3)"
      using sync_head_chain sync_chunk_eq by simp
    show ?thesis
      by (rule ro_absorb_lookup_chain_functional[
            OF sync_chain witness_head_chain])
  qed
  have witness_counter_ws3:
      "PQueryCounter ws3 = Suc (PQueryCounter builder)"
    by (rule ro_checked_staged_query_record_state_counter[
          OF controlled i_bound witness_challenge witness_stage
            witness_record'])
  have sent_mid: "sent \<le> verifier_mid"
    by (rule hash_ext_trans[OF Suc.prems(3) verifier_step_ext])
  have tail_state_eq: "PState verifier_mid = PState ws3"
    using state_mid_sync head_state_eq by simp
  have tail_counter_eq:
      "PQueryCounter verifier_mid = PQueryCounter ws3"
    using counter_mid witness_counter_ws3 by simp
  have tail_transcript:
      "PTranscript verifier_mid = List.concat chunks_tail @ rest"
    using transcript_mid sync_chunks_tail_eq by simp

  from ro_verifier_query_round_program_authenticated_trace_openings_zero[
      OF f_fl_zero verifier_head]
  obtain auth_raw auth_idx fv trace_openings where
    auth_idx_eq: "auth_idx = index (to_nat auth_raw)"
    and auth_lookup:
      "fmlookup (HashMap verifier_mid)
        (QueryIndexChallenge
          (PQueryCounter verifier_state) (PState verifier_state)) =
        Some auth_raw"
    and trace_len:
      "length trace_openings = length (powers_scaled auth_idx)"
    and trace_values: "map opening_value trace_openings = fv"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled auth_idx"
    and trace_table_mid:
      "partial_authenticated_table fr (scale * clength)
        trace_openings verifier_mid"
    and trace_final:
      "opening_value (trace_openings ! 0) = f_final"
    .
  have witness_lookup_mid:
      "fmlookup (HashMap verifier_mid)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some witness_raw"
    by (rule hash_extension_lookup[OF witness_recorded sent_mid])
  have auth_raw_eq: "auth_raw = witness_raw"
    using auth_lookup witness_lookup_mid Suc.prems(4) Suc.prems(5)
    by simp
  have auth_idx_eq_witness:
      "auth_idx = index (to_nat witness_raw)"
    using auth_idx_eq auth_raw_eq by simp

  from Suc.IH[OF tail_bound witness_tail sent_mid tail_state_eq
      tail_counter_eq tail_transcript verifier_tail]
  obtain trace_tail_at where
    tail_result:
      "verifier_mid \<le> verifier_final \<and>
       length raws_tail = n \<and>
       length query_states_tail = n \<and>
       length chunks_tail = n \<and>
       (\<forall>j < n.
         map opening_index (trace_tail_at j) =
           powers_scaled (index (to_nat (raws_tail ! j))) \<and>
         partial_authenticated_table fr (scale * clength)
           (trace_tail_at j) verifier_final \<and>
         opening_value (trace_tail_at j ! 0) = f_final)"
    by blast
  have verifier_mid_final: "verifier_mid \<le> verifier_final"
    using tail_result by simp
  have trace_table_final:
      "partial_authenticated_table fr (scale * clength)
        trace_openings verifier_final"
    by (rule partial_authenticated_table_mono[
          OF trace_table_mid verifier_mid_final])

  have verifier_ext_final: "verifier_state \<le> verifier_final"
    by (rule hash_ext_trans[OF verifier_step_ext verifier_mid_final])
  have tail_lengths:
      "length raws_tail = n \<and>
       length query_states_tail = n \<and>
       length chunks_tail = n"
    using tail_result by simp
  have tail_evidence:
      "\<forall>j < n.
        map opening_index (trace_tail_at j) =
          powers_scaled (index (to_nat (raws_tail ! j))) \<and>
        partial_authenticated_table fr (scale * clength)
          (trace_tail_at j) verifier_final \<and>
        opening_value (trace_tail_at j ! 0) = f_final"
    using tail_result by simp
  let ?trace_at =
    "\<lambda>j. case j of 0 \<Rightarrow> trace_openings | Suc k \<Rightarrow> trace_tail_at k"
  have all_evidence:
      "\<forall>j < Suc n.
        map opening_index (?trace_at j) =
          powers_scaled (index (to_nat (raws ! j))) \<and>
        partial_authenticated_table fr (scale * clength)
          (?trace_at j) verifier_final \<and>
        opening_value (?trace_at j ! 0) = f_final"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show
      "map opening_index (?trace_at j) =
          powers_scaled (index (to_nat (raws ! j))) \<and>
       partial_authenticated_table fr (scale * clength)
          (?trace_at j) verifier_final \<and>
       opening_value (?trace_at j ! 0) = f_final"
    proof (cases j)
      case 0
      show ?thesis
        using trace_indices trace_table_final trace_final
          auth_idx_eq_witness raws_eq
        unfolding 0
        by simp
    next
      case (Suc k)
      have k_bound: "k < n"
        using j_bound Suc by simp
      have tail_at_k:
          "map opening_index (trace_tail_at k) =
             powers_scaled (index (to_nat (raws_tail ! k))) \<and>
           partial_authenticated_table fr (scale * clength)
             (trace_tail_at k) verifier_final \<and>
           opening_value (trace_tail_at k ! 0) = f_final"
        by (rule tail_evidence[rule_format, OF k_bound])
      show ?thesis
        using tail_at_k raws_eq
        unfolding Suc
        by simp
    qed
  qed
  show ?case
    by (intro exI[of _ ?trace_at])
      (use verifier_ext_final tail_lengths raws_eq query_states_eq chunks_eq
        all_evidence in simp)
qed

end
end
