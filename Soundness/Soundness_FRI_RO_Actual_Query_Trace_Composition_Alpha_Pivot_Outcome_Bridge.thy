(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Outcome_Bridge.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Outcome_Bridge
  imports
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Adaptive_Query_Budget
begin

context soundness
begin

lemma ro_staged_alpha_program_lookup_prefix:
  assumes outcome:
    "Some (as, t) \<in> set_dist (execute (ro_staged_alpha_program n) s)"
  shows
    "ro_alpha_lookup_prefix (HashMap t)
       (PAlphaCounter s) (PState s) as (PState t) \<and>
     s \<le> t"
  using outcome
proof (induction n arbitrary: s as t)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain a s1 s2 as_tail where
    challenge_out:
      "Some (a, s1) \<in> set_dist (execute receive_alpha_challenge s)"
    and record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message a) s1)"
    and tail_out:
      "Some (as_tail, t) \<in>
        set_dist (execute (ro_staged_alpha_program n) s2)"
    and as_eq: "as = a # as_tail"
    unfolding ro_staged_alpha_program.simps
    by (auto elim!: set_dist_bindE)
  have challenge_props:
      "s \<le> s1 \<and>
       PState s1 = PState s \<and>
       fmlookup (HashMap s1)
         (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using receive_alpha_challenge_outcome[OF challenge_out]
    by simp
  have challenge_counter:
      "PAlphaCounter s1 = Suc (PAlphaCounter s)"
    using receive_alpha_challenge_counter_outcome[OF challenge_out]
    by simp
  have record_props:
      "fmlookup (HashMap s2) (TranscriptAbsorb (PState s1) a) =
         Some (PState s2) \<and>
       s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[OF record_out])
  have record_counter:
      "PAlphaCounter s2 = PAlphaCounter s1"
    using ro_record_staged_message_counter_preserves[OF record_out]
    by simp
  have tail_props:
      "ro_alpha_lookup_prefix (HashMap t)
         (PAlphaCounter s2) (PState s2) as_tail (PState t) \<and>
       s2 \<le> t"
    by (rule Suc.IH[OF tail_out])
  have challenge_lookup_s1:
      "fmlookup (HashMap s1)
         (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using challenge_props by simp
  have challenge_lookup_s2:
      "fmlookup (HashMap s2)
         (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    by (rule hash_extension_lookup[
          OF challenge_lookup_s1 conjunct2[OF record_props]])
  have challenge_lookup_t:
      "fmlookup (HashMap t)
         (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    by (rule hash_extension_lookup[
          OF challenge_lookup_s2 conjunct2[OF tail_props]])
  have absorb_lookup_t:
      "fmlookup (HashMap t)
         (TranscriptAbsorb (PState s) a) = Some (PState s2)"
  proof -
    have "fmlookup (HashMap t)
        (TranscriptAbsorb (PState s1) a) = Some (PState s2)"
      by (rule hash_extension_lookup[
            OF conjunct1[OF record_props] conjunct2[OF tail_props]])
    then show ?thesis
      using challenge_props by simp
  qed
  have prefix:
      "ro_alpha_lookup_prefix (HashMap t)
         (PAlphaCounter s) (PState s) as (PState t)"
    unfolding as_eq
    using challenge_lookup_t absorb_lookup_t tail_props
      challenge_counter record_counter
    by auto
  have ext_s_s2: "s \<le> s2"
    by (rule hash_ext_trans[
          OF conjunct1[OF challenge_props] conjunct2[OF record_props]])
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_s2 conjunct2[OF tail_props]])
  show ?case
    using prefix ext_s_t by simp
qed


lemma ro_alpha_lookup_prefix_mono:
  assumes chain:
      "ro_alpha_lookup_prefix (HashMap s) c st as final"
    and ext: "s \<le> t"
  shows "ro_alpha_lookup_prefix (HashMap t) c st as final"
  using chain
proof (induction as arbitrary: c st)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then obtain st' where
    challenge:
      "fmlookup (HashMap s) (AlphaChallenge c st) = Some a"
    and absorb:
      "fmlookup (HashMap s) (TranscriptAbsorb st a) = Some st'"
    and tail:
      "ro_alpha_lookup_prefix (HashMap s) (Suc c) st' as final"
    by auto
  have challenge_t:
      "fmlookup (HashMap t) (AlphaChallenge c st) = Some a"
    by (rule hash_extension_lookup[OF challenge ext])
  have absorb_t:
      "fmlookup (HashMap t) (TranscriptAbsorb st a) = Some st'"
    by (rule hash_extension_lookup[OF absorb ext])
  have tail_t:
      "ro_alpha_lookup_prefix (HashMap t) (Suc c) st' as final"
    by (rule Cons.IH[OF tail])
  show ?case
    using challenge_t absorb_t tail_t by auto
qed


lemma ro_alpha_lookup_prefix_take_lookup:
  assumes chain: "ro_alpha_lookup_prefix M c st as final"
    and bound: "i < length as"
  shows
    "\<exists>pivot_state.
      ro_alpha_lookup_prefix M c st (take i as) pivot_state \<and>
      fmlookup M (AlphaChallenge (c + i) pivot_state) = Some (as ! i)"
  using chain bound
proof (induction i arbitrary: c st as)
  case 0
  then obtain a rest where
    as_eq: "as = a # rest"
    and challenge:
      "fmlookup M (AlphaChallenge c st) = Some a"
    by (cases as) auto
  show ?case
    using as_eq challenge by auto
next
  case (Suc i)
  from Suc.prems obtain a rest st' where
    as_eq: "as = a # rest"
    and challenge:
      "fmlookup M (AlphaChallenge c st) = Some a"
    and absorb:
      "fmlookup M (TranscriptAbsorb st a) = Some st'"
    and tail_chain:
      "ro_alpha_lookup_prefix M (Suc c) st' rest final"
    by (cases as) auto
  have tail_bound: "i < length rest"
    using Suc.prems(2) as_eq by simp
  from Suc.IH[OF tail_chain tail_bound]
  obtain pivot_state where
    prefix_tail:
      "ro_alpha_lookup_prefix M (Suc c) st' (take i rest) pivot_state"
    and lookup:
      "fmlookup M
        (AlphaChallenge (Suc c + i) pivot_state) = Some (rest ! i)"
    by blast
  have prefix:
      "ro_alpha_lookup_prefix M c st (take (Suc i) as) pivot_state"
    using as_eq challenge absorb prefix_tail by auto
  have lookup':
      "fmlookup M
        (AlphaChallenge (c + Suc i) pivot_state) = Some (as ! Suc i)"
    using lookup as_eq by simp
  show ?case
    using prefix lookup' by blast
qed


lemma ro_checked_staged_transcript_program_alpha_lookup_chain:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, t) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A) s)"
  shows
    "\<exists>alpha_start alpha_final.
      ro_absorb_lookup_chain t (PState s)
        ([staged_trace_root data] @
          staged_trace_fri_roots data @
          [staged_trace_final data])
        alpha_start \<and>
      ro_alpha_lookup_prefix (HashMap t)
        (PAlphaCounter s) alpha_start
        (staged_alphas data) alpha_final"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3
      trace_final s4 s5 as s6 dg s7 s8 s9
      composition_roots composition_bs s10 composition_final s11 s12
      query_chunks where
    root_out:
      "Some (fr, s1) \<in> set_dist (execute (trace_root_stage A) s)"
    and root_record_out:
      "Some ((), s2) \<in>
        set_dist (execute (ro_record_staged_message fr) s1)"
    and trace_out:
      "Some ((trace_roots, trace_bs), s3) \<in>
        set_dist
          (execute
            (ro_staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and trace_final_out:
      "Some (trace_final, s4) \<in>
        set_dist (execute (trace_final_stage A trace_bs) s3)"
    and trace_final_record_out:
      "Some ((), s5) \<in>
        set_dist (execute (ro_record_staged_message trace_final) s4)"
    and alpha_out:
      "Some (as, s6) \<in>
        set_dist (execute (ro_staged_alpha_program (length spec)) s5)"
    and degree_out:
      "Some (dg, s7) \<in> set_dist (execute (degree_stage A as) s6)"
    and degree_record_out:
      "Some ((), s8) \<in>
        set_dist (execute (ro_record_staged_message dg) s7)"
    and assert_out:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1))) s8)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s10) \<in>
        set_dist
          (execute
            (ro_staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s9)"
    and composition_final_out:
      "Some (composition_final, s11) \<in>
        set_dist
          (execute (composition_final_stage A dg composition_bs) s10)"
    and composition_final_record_out:
      "Some ((), s12) \<in>
        set_dist
          (execute (ro_record_staged_message composition_final) s11)"
    and query_out:
      "Some (query_chunks, t) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              0 rounds) s12)"
    and data_eq:
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
    unfolding ro_checked_staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)

  have root_controlled:
      "controlled_ro_program (trace_root_budget budgets)
        (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have root_ext: "s \<le> s1"
    using controlled_ro_program_extension[OF root_controlled] root_out
    unfolding hash_extension_preserving_def by blast
  have root_state: "PState s1 = PState s"
    and root_alpha_counter: "PAlphaCounter s1 = PAlphaCounter s"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp_all
  have root_record_props:
      "fmlookup (HashMap s2) (TranscriptAbsorb (PState s1) fr) =
          Some (PState s2) \<and>
       s1 \<le> s2"
    by (rule ro_record_staged_message_absorb_lookup_state[
          OF root_record_out])
  have root_record_counter:
      "PAlphaCounter s2 = PAlphaCounter s1"
    using ro_record_staged_message_counter_preserves[OF root_record_out]
    by simp
  have root_chain_s2:
      "ro_absorb_lookup_chain s2 (PState s) [fr] (PState s2)"
    using root_record_props root_state by auto

  have trace_bound:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have trace_props:
      "ro_absorb_lookup_chain s3 (PState s2) trace_roots (PState s3) \<and>
       s2 \<le> s3"
    by (rule ro_staged_trace_fri_program_absorb_lookup_chain[
          OF controlled trace_bound trace_out])
  have trace_counters:
      "PAlphaCounter s3 = PAlphaCounter s2"
    using ro_staged_trace_fri_program_counters[
      OF controlled trace_bound trace_out]
    by simp
  have root_chain_s3:
      "ro_absorb_lookup_chain s3 (PState s) [fr] (PState s2)"
    by (rule ro_absorb_lookup_chain_mono[
          OF root_chain_s2 conjunct2[OF trace_props]])
  have root_trace_chain_s3:
      "ro_absorb_lookup_chain s3 (PState s)
        ([fr] @ trace_roots) (PState s3)"
    by (rule ro_absorb_lookup_chain_append[
          OF root_chain_s3 conjunct1[OF trace_props]])

  have trace_final_controlled:
      "controlled_ro_program (trace_final_budget budgets)
        (trace_final_stage A trace_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have trace_final_ext: "s3 \<le> s4"
    using controlled_ro_program_extension[OF trace_final_controlled]
      trace_final_out
    unfolding hash_extension_preserving_def by blast
  have trace_final_state: "PState s4 = PState s3"
    and trace_final_alpha_counter:
      "PAlphaCounter s4 = PAlphaCounter s3"
    using controlled_stage_outcome_fields[
      OF trace_final_controlled trace_final_out]
    by simp_all
  have trace_final_record_props:
      "fmlookup (HashMap s5)
          (TranscriptAbsorb (PState s4) trace_final) =
          Some (PState s5) \<and>
       s4 \<le> s5"
    by (rule ro_record_staged_message_absorb_lookup_state[
          OF trace_final_record_out])
  have trace_final_record_counter:
      "PAlphaCounter s5 = PAlphaCounter s4"
    using ro_record_staged_message_counter_preserves[
      OF trace_final_record_out]
    by simp
  have s3_s5: "s3 \<le> s5"
    by (rule hash_ext_trans[
          OF trace_final_ext conjunct2[OF trace_final_record_props]])
  have root_trace_chain_s5:
      "ro_absorb_lookup_chain s5 (PState s)
        ([fr] @ trace_roots) (PState s3)"
    by (rule ro_absorb_lookup_chain_mono[
          OF root_trace_chain_s3 s3_s5])
  have trace_final_chain_s5:
      "ro_absorb_lookup_chain s5 (PState s3)
        [trace_final] (PState s5)"
    using trace_final_record_props trace_final_state by auto
  have prealpha_chain_s5:
      "ro_absorb_lookup_chain s5 (PState s)
        ([fr] @ trace_roots @ [trace_final]) (PState s5)"
    using ro_absorb_lookup_chain_append[
      OF root_trace_chain_s5 trace_final_chain_s5]
    by simp
  have alpha_start_counter:
      "PAlphaCounter s5 = PAlphaCounter s"
    using root_alpha_counter root_record_counter trace_counters
      trace_final_alpha_counter trace_final_record_counter
    by simp
  have alpha_props:
      "ro_alpha_lookup_prefix (HashMap s6)
          (PAlphaCounter s5) (PState s5) as (PState s6) \<and>
       s5 \<le> s6"
    by (rule ro_staged_alpha_program_lookup_prefix[OF alpha_out])

  have degree_controlled:
      "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have degree_ext: "s6 \<le> s7"
    using controlled_ro_program_extension[OF degree_controlled] degree_out
    unfolding hash_extension_preserving_def by blast
  have degree_record_props:
      "fmlookup (HashMap s8) (TranscriptAbsorb (PState s7) dg) =
          Some (PState s8) \<and>
       s7 \<le> s8"
    by (rule ro_record_staged_message_absorb_lookup_state[
          OF degree_record_out])
  have s9_eq: "s9 = s8"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_round_bound:
      "0 + ceil_log (to_nat dg + 1) \<le>
        length (composition_fri_budgets budgets)"
    using assert_out wf
    unfolding assert_def staged_budget_wellformed_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_props_s9:
      "ro_absorb_lookup_chain s10 (PState s9) composition_roots
          (PState s10) \<and>
       s9 \<le> s10"
    by (rule ro_staged_composition_fri_program_absorb_lookup_chain[
          OF controlled composition_round_bound composition_out])
  have composition_final_controlled:
      "controlled_ro_program (composition_final_budget budgets)
        (composition_final_stage A dg composition_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_final_ext: "s10 \<le> s11"
    using controlled_ro_program_extension[
      OF composition_final_controlled] composition_final_out
    unfolding hash_extension_preserving_def by blast
  have composition_final_record_props:
      "fmlookup (HashMap s12)
          (TranscriptAbsorb (PState s11) composition_final) =
          Some (PState s12) \<and>
       s11 \<le> s12"
    by (rule ro_record_staged_message_absorb_lookup_state[
          OF composition_final_record_out])
  have query_bound:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_props:
      "ro_absorb_lookup_chain t (PState s12)
          (List.concat query_chunks) (PState t) \<and>
       s12 \<le> t"
    by (rule ro_checked_staged_query_program_absorb_lookup_chain[
          OF controlled query_bound query_out])

  have s6_s8: "s6 \<le> s8"
    by (rule hash_ext_trans[
          OF degree_ext conjunct2[OF degree_record_props]])
  have s8_s10: "s8 \<le> s10"
    using s9_eq composition_props_s9 by simp
  have s6_s10: "s6 \<le> s10"
    by (rule hash_ext_trans[OF s6_s8 s8_s10])
  have s6_s12: "s6 \<le> s12"
    by (rule hash_ext_trans[
          OF hash_ext_trans[
            OF s6_s10 composition_final_ext]
          conjunct2[OF composition_final_record_props]])
  have s6_t: "s6 \<le> t"
    by (rule hash_ext_trans[
          OF s6_s12 conjunct2[OF query_props]])
  have s5_t: "s5 \<le> t"
    by (rule hash_ext_trans[OF conjunct2[OF alpha_props] s6_t])

  have prealpha_chain_t:
      "ro_absorb_lookup_chain t (PState s)
        ([fr] @ trace_roots @ [trace_final]) (PState s5)"
    by (rule ro_absorb_lookup_chain_mono[OF prealpha_chain_s5 s5_t])
  have alpha_chain_t:
      "ro_alpha_lookup_prefix (HashMap t)
        (PAlphaCounter s) (PState s5) as (PState s6)"
    using ro_alpha_lookup_prefix_mono[
      OF conjunct1[OF alpha_props] s6_t]
      alpha_start_counter
    by simp
  show ?thesis
    using prealpha_chain_t alpha_chain_t data_eq by auto
qed



lemma ro_checked_staged_transcript_program_with_first_root_prefix_canonical:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
  shows
    "prefix =
        (staged_trace_root data, [],
          hd (staged_trace_fri_roots data)) \<and>
     prefix_state \<le> attacker_state"
proof -
  from ro_checked_staged_transcript_program_with_first_root_outcomeE[
    OF outcome]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute
            (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
    and after_out:
      "Some (head_data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program
              A prefix)
            prefix_final)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    by blast
  obtain fr trace_bs first_root where
    prefix_eq: "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  have prefix_props:
      "trace_bs = [] \<and> prefix_state = prefix_final"
    using ro_staged_first_trace_fri_root_prefix_program_chain[
      OF wf controlled nonempty prefix_out[unfolded prefix_eq]]
    by blast
  have after_fields:
      "staged_trace_root head_data = fr \<and>
       (\<exists>roots. staged_trace_fri_roots head_data = first_root # roots)"
    by (rule
      ro_checked_staged_after_first_trace_fri_root_prefix_program_fields[
        OF nonempty])
      (use after_out prefix_eq in simp)
  obtain trace_roots where
    trace_root_eq: "staged_trace_root data = fr"
    and trace_roots_eq:
      "staged_trace_fri_roots data = first_root # trace_roots"
    using after_fields data_eq by auto
  have canonical:
      "prefix =
        (staged_trace_root data, [],
          hd (staged_trace_fri_roots data))"
    using prefix_eq prefix_props trace_root_eq trace_roots_eq by simp
  have good_fields:
      "prefix_state \<le> attacker_state \<and>
       PQueryCounter query_start = 0"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_good_fields[
        OF wf controlled nonempty outcome])
  show ?thesis
    using canonical good_fields by blast
qed



lemma trace_composition_bad_alpha_imp_alpha_pivot_relation_transition:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values attacker_state"
    and no_trace_merkle:
      "\<not> hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state attacker_state"
    and as_bad:
      "staged_alphas data \<in>
        composition_trace_bad_alpha_space
          (first_trace_fri_root_prefix_first_table prefix prefix_state)"
  shows
    "hash_state_relation_transition
      (alpha_pivot_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
  have canonical_props:
      "prefix =
          (staged_trace_root data, [],
            hd (staged_trace_fri_roots data)) \<and>
       prefix_state \<le> attacker_state"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_prefix_canonical[
        OF wf controlled nonempty outcome])
  then have prefix_eq:
      "prefix =
        (staged_trace_root data, [],
          hd (staged_trace_fri_roots data))"
    and prefix_ext: "prefix_state \<le> attacker_state"
    by blast+

  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome[
        OF nonempty outcome])
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_alphas data) = length spec"
    using ro_checked_staged_transcript_program_outcome_shape[
      OF original_out]
    by blast
  have trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    and alpha_len: "length (staged_alphas data) = length spec"
    using shape by blast+
  have trace_nonempty: "staged_trace_fri_roots data \<noteq> []"
    using trace_len nonempty by auto
  from ro_checked_staged_transcript_program_alpha_lookup_chain[
    OF wf controlled original_out]
  obtain alpha_start alpha_final where
    prealpha_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state)
        ([staged_trace_root data] @
          staged_trace_fri_roots data @
          [staged_trace_final data])
        alpha_start"
    and alpha_chain:
      "ro_alpha_lookup_prefix (HashMap attacker_state)
        (PAlphaCounter adversary_initial_state)
        alpha_start (staged_alphas data) alpha_final"
    by blast

  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision attacker_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_ext])
    then show False using clean by contradiction
  qed
  have no_trace_merkle':
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets
          {staged_trace_root data, hd (staged_trace_fri_roots data)}
          prefix_state)
        prefix_state attacker_state"
    using no_trace_merkle prefix_clean
    unfolding prefix_eq first_trace_fri_root_prefix_merkle_targets_def
    by simp
  have first_targets:
      "merkle_prefix_path_targets
          {hd (staged_trace_fri_roots data)} prefix_state
        \<subseteq>
       merkle_prefix_path_targets
          {staged_trace_root data, hd (staged_trace_fri_roots data)}
          prefix_state"
    by (rule merkle_prefix_path_targets_mono) auto
  have no_first:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets
          {hd (staged_trace_fri_roots data)} prefix_state)
        prefix_state attacker_state"
    using no_trace_merkle'
      hash_map_new_output_hit_subset[OF first_targets]
    by blast

  let ?final = "channel_for_hash_map (HashMap attacker_state)"
  have final_map: "HashMap ?final = HashMap attacker_state"
    unfolding channel_for_hash_map_def by simp
  have first_final:
      "first_trace_fri_root_prefix_first_table
          (staged_trace_root data, [],
            hd (staged_trace_fri_roots data))
          ?final =
       first_trace_fri_root_prefix_first_table
          (staged_trace_root data, [],
            hd (staged_trace_fri_roots data))
          prefix_state"
  proof -
    have final_attacker:
        "conceptual_table ?final
            (hd (staged_trace_fri_roots data)) (scale * clength) =
         conceptual_table attacker_state
            (hd (staged_trace_fri_roots data)) (scale * clength)"
      by (rule conceptual_table_cong_hash_map[OF final_map])
    have attacker_prefix:
        "conceptual_table attacker_state
            (hd (staged_trace_fri_roots data)) (scale * clength) =
         conceptual_table prefix_state
            (hd (staged_trace_fri_roots data)) (scale * clength)"
      by (rule conceptual_table_prefix_stable_if_no_target[
        OF prefix_ext no_first])
    show ?thesis
      unfolding first_trace_fri_root_prefix_first_table_def
      using final_attacker attacker_prefix by simp
  qed
  have as_bad_final:
      "staged_alphas data \<in>
        composition_trace_bad_alpha_space
          (first_trace_fri_root_prefix_first_table
            (staged_trace_root data, [],
              hd (staged_trace_fri_roots data))
            ?final)"
    using as_bad prefix_eq first_final by simp
  have violated:
      "violated_constraints
        (low_degree_trace_witness
          (first_trace_fri_root_prefix_first_table
            (staged_trace_root data, [],
              hd (staged_trace_fri_roots data))
            ?final)) \<noteq> {}"
    by (rule composition_trace_bad_alpha_space_violated[OF as_bad_final])
  let ?pivot =
    "composition_alpha_pivot
      (low_degree_trace_witness
        (first_trace_fri_root_prefix_first_table
          (staged_trace_root data, [],
            hd (staged_trace_fri_roots data))
          ?final))"
  have pivot_spec: "?pivot < length spec"
    by (rule composition_alpha_pivot_bound[OF violated])
  have pivot_bound: "?pivot < length (staged_alphas data)"
    using pivot_spec alpha_len by simp
  from ro_alpha_lookup_prefix_take_lookup[
    OF alpha_chain pivot_bound]
  obtain pivot_state where
    alpha_prefix:
      "ro_alpha_lookup_prefix (HashMap attacker_state)
        (PAlphaCounter adversary_initial_state)
        alpha_start (take ?pivot (staged_alphas data)) pivot_state"
    and pivot_lookup:
      "fmlookup (HashMap attacker_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state) =
        Some (staged_alphas data ! ?pivot)"
    by blast
  have pivot_member:
      "staged_alphas data ! ?pivot \<in>
        composition_trace_bad_alpha_pivot_values
          (first_trace_fri_root_prefix_first_table
            (staged_trace_root data, [],
              hd (staged_trace_fri_roots data))
            ?final)
          (take ?pivot (staged_alphas data))"
    by (rule
      composition_trace_bad_alpha_pivot_value_member[OF as_bad_final])
  have prefix_length:
      "length (take ?pivot (staged_alphas data)) = ?pivot"
    using pivot_bound by simp

  have prealpha_final:
      "ro_absorb_lookup_chain ?final
        (PState adversary_initial_state)
        ([staged_trace_root data] @
          staged_trace_fri_roots data @
          [staged_trace_final data])
        alpha_start"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule prealpha_chain)
  have clean_final: "\<not> hash_map_output_collision ?final"
    using clean final_map
    unfolding hash_map_output_collision_def by simp
  have no_initial_final:
      "PState adversary_initial_state \<notin> hash_map_output_values ?final"
    using no_initial final_map
    unfolding hash_map_output_values_def by simp
  have trace_table_eq:
      "alpha_pivot_trace_table (HashMap attacker_state)
          (staged_trace_root data) (staged_trace_fri_roots data) =
       first_trace_fri_root_prefix_first_table
          (staged_trace_root data, [], hd (staged_trace_fri_roots data))
          ?final"
    by (rule alpha_pivot_trace_table_nonempty[OF trace_nonempty])
  have relation:
      "alpha_pivot_absorbed_query_relation
        (HashMap attacker_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state)
        (staged_alphas data ! ?pivot)"
    unfolding alpha_pivot_absorbed_query_relation_def Let_def
  proof (intro conjI)
    show "\<not> hash_map_output_collision ?final"
      by (rule clean_final)
    show "PState adversary_initial_state \<notin> hash_map_output_values ?final"
      by (rule no_initial_final)
    show
      "\<exists>fr trace_roots trace_final alpha_start' alpha_prefix pivot_state'.
        length trace_roots = ceil_log clength \<and>
        ro_absorb_lookup_chain ?final
          (PState adversary_initial_state)
          ([fr] @ trace_roots @ [trace_final]) alpha_start' \<and>
        ro_alpha_lookup_prefix (HashMap attacker_state)
          (PAlphaCounter adversary_initial_state)
          alpha_start' alpha_prefix pivot_state' \<and>
        length alpha_prefix =
          composition_alpha_pivot
            (low_degree_trace_witness
              (alpha_pivot_trace_table
                (HashMap attacker_state) fr trace_roots)) \<and>
        AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state =
          AlphaChallenge
            (PAlphaCounter adversary_initial_state + length alpha_prefix)
            pivot_state' \<and>
        staged_alphas data ! ?pivot \<in>
          composition_trace_bad_alpha_pivot_values
            (alpha_pivot_trace_table
              (HashMap attacker_state) fr trace_roots)
            alpha_prefix"
    proof (rule exI[of _ "staged_trace_root data"],
        rule exI[of _ "staged_trace_fri_roots data"],
        rule exI[of _ "staged_trace_final data"],
        rule exI[of _ alpha_start],
        rule exI[of _ "take ?pivot (staged_alphas data)"],
        rule exI[of _ pivot_state],
        intro conjI)
      show "length (staged_trace_fri_roots data) = ceil_log clength"
        by (rule trace_len)
      show
        "ro_absorb_lookup_chain ?final
          (PState adversary_initial_state)
          ([staged_trace_root data] @ staged_trace_fri_roots data @
            [staged_trace_final data])
          alpha_start"
        by (rule prealpha_final)
      show
        "ro_alpha_lookup_prefix (HashMap attacker_state)
          (PAlphaCounter adversary_initial_state)
          alpha_start (take ?pivot (staged_alphas data)) pivot_state"
        by (rule alpha_prefix)
      show
        "length (take ?pivot (staged_alphas data)) =
          composition_alpha_pivot
            (low_degree_trace_witness
              (alpha_pivot_trace_table
                (HashMap attacker_state)
                (staged_trace_root data)
                (staged_trace_fri_roots data)))"
        using prefix_length trace_table_eq by simp
      show
        "AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state =
         AlphaChallenge
          (PAlphaCounter adversary_initial_state +
            length (take ?pivot (staged_alphas data)))
          pivot_state"
        using prefix_length by simp
      show
        "staged_alphas data ! ?pivot \<in>
          composition_trace_bad_alpha_pivot_values
            (alpha_pivot_trace_table
              (HashMap attacker_state)
              (staged_trace_root data)
              (staged_trace_fri_roots data))
            (take ?pivot (staged_alphas data))"
        using pivot_member trace_table_eq by simp
    qed
  qed
  have map_bound:
      "card (fmdom' (HashMap attacker_state)) \<le>
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound[
        OF wf controlled nonempty outcome clean])
  have bounded_relation:
      "alpha_pivot_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        (HashMap attacker_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state)
        (staged_alphas data ! ?pivot)"
    unfolding alpha_pivot_absorbed_query_relation_bounded_def
    using map_bound relation by simp
  have active:
      "hash_state_relation_active
        (alpha_pivot_absorbed_query_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets))
        (HashMap attacker_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state)
        (staged_alphas data ! ?pivot)"
    unfolding hash_state_relation_active_def
    using pivot_lookup bounded_relation by simp
  have inactive_initial:
      "\<not> hash_state_relation_active
        (alpha_pivot_absorbed_query_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets))
        (HashMap adversary_initial_state)
        (AlphaChallenge
          (PAlphaCounter adversary_initial_state + ?pivot)
          pivot_state)
        (staged_alphas data ! ?pivot)"
    unfolding hash_state_relation_active_def adversary_initial_state_def
    by simp
  show ?thesis
    unfolding hash_state_relation_transition_def
    using active inactive_initial by blast
qed


end
end
