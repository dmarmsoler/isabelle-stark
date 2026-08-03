(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Augmented.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Augmented
  imports Staged_Security_Experiment_Composition_Query_Bridge
begin

text \<open>
  Augmented query-prefix events for the composition query side.

  These events live in the query-prefix augmented experiment, so the sampled
  query challenge is part of the event output.  This is the correct setting
  for applying fixed-witness query-prefix bounds.  The fixed-witness event
  below deliberately does not existentially choose openings after the query
  challenge; the remaining public-proof work is to derive such fixed witnesses
  from pre-query Merkle/candidate evidence or charge failures to existing side
  events.
\<close>

context soundness
begin

lemma checked_staged_security_with_data_state_query_prefix_continuationE:
  assumes i_bound: "i < rounds"
    and support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
  obtains prefix prefix_state raw raw_state where
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute
          (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive_with_verifier A i
            ((prefix, prefix_state), raw))
          raw_state)"
proof -
  have decomp:
    "checked_staged_security_experiment_with_data_state A =
      checked_staged_query_prefix_receive_with_state A i \<bind>
        checked_staged_after_query_prefix_receive_with_verifier A i"
    by (rule
        checked_staged_security_experiment_with_data_state_query_prefix_receive_decomp
        [OF i_bound])
  from support[unfolded decomp]
  obtain x raw_state where prefix_receive:
      "Some (x, raw_state) \<in>
        set_dist
          (execute
            (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and continuation:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive_with_verifier A i x)
            raw_state)"
    by (auto elim!: set_dist_bindE)
  obtain prefix_pack raw where x_eq: "x = (prefix_pack, raw)"
    by (cases x) simp
  obtain prefix prefix_state where prefix_pack_eq:
    "prefix_pack = (prefix, prefix_state)"
    by (cases prefix_pack) simp
  show ?thesis
    by (rule that[of prefix prefix_state raw raw_state])
      (use prefix_receive continuation x_eq prefix_pack_eq in simp_all)
qed

definition checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
where
  "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        staged_composition_fri_roots data \<noteq> [] \<and>
        (trace_openings, composition_openings) \<in>
          query_header_supported_partial_opening_witnesses
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) \<and>
        checked_staged_security_with_actual_query_prefix_candidate_opening_hit
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i out)"

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_imp_actual:
  assumes hit:
    "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i out"
  shows
    "checked_staged_security_with_actual_query_prefix_candidate_opening_hit
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      i out"
  using hit
  unfolding
    checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_def
  by (cases out) (auto split: prod.splits)

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hitE:
  assumes hit:
    "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
  obtains
    "staged_composition_fri_roots data \<noteq> []"
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
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state"
proof -
  have comp_nonempty:
    "staged_composition_fri_roots data \<noteq> []"
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
    and actual:
    "checked_staged_security_with_actual_query_prefix_candidate_opening_hit
      ((replicate rounds []) [i := trace_openings])
      ((replicate rounds []) [i := composition_openings])
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    using hit
    unfolding
      checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_def
    by simp_all
  from checked_staged_security_with_actual_query_prefix_candidate_opening_hitE
      [OF actual]
  have target:
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state"
    .
  show ?thesis
    by (rule that[OF comp_nonempty witness target])
qed

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_prefix_facts:
  assumes support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
        trace_openings composition_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "staged_alphas data = sqp_alphas prefix"
    "staged_trace_root data = sqp_trace_root prefix"
    "staged_composition_fri_roots data = sqp_composition_fri_roots prefix"
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state"
proof -
  show alphas: "staged_alphas data = sqp_alphas prefix"
    by (rule checked_staged_security_with_query_prefix_data_state_alphas_eq)
      (rule support)
  from hit show target:
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state"
    by (rule
        checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hitE)
  from support show "staged_trace_root data = sqp_trace_root prefix"
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
      checked_staged_after_query_prefix_receive_with_verifier_def
      checked_staged_after_query_prefix_receive_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  from support show
    "staged_composition_fri_roots data = sqp_composition_fri_roots prefix"
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
      checked_staged_after_query_prefix_receive_with_verifier_def
      checked_staged_after_query_prefix_receive_def
    by (auto elim!: set_dist_bindE split: prod.splits)
qed

text \<open>
  The next wrapper lets downstream composition proofs conjoin their own
  side-condition with the fixed authenticated-opening query-prefix hit, without
  changing the probability bound.  This is deliberately fixed-witness: the
  trace and composition openings are chosen before the query challenge is
  sampled.
\<close>

definition checked_staged_security_with_query_prefix_fixed_header_component
where
  "checked_staged_security_with_query_prefix_fixed_header_component
      E trace_openings composition_openings i out \<longleftrightarrow>
    E out \<and>
    checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i out"

definition checked_staged_security_with_query_prefix_fixed_current_authenticated_component
where
  "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
      E trace_openings composition_openings i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_fixed_header_component
      E trace_openings composition_openings i out \<and>
    checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_openings composition_openings i out"

definition checked_staged_security_with_query_prefix_header_witness_not_current
where
  "checked_staged_security_with_query_prefix_header_witness_not_current
      E trace_openings composition_openings i out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_fixed_header_component
      E trace_openings composition_openings i out \<and>
    \<not> checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_openings composition_openings i out"

definition checked_staged_security_with_query_prefix_header_witness_path_output_hit
where
  "checked_staged_security_with_query_prefix_header_witness_path_output_hit
      E trace_openings composition_openings i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        E out \<and>
        staged_composition_fri_roots data \<noteq> [] \<and>
        (\<exists>witness_result witness_state rest.
          let s = verifier_state_from_adversary attacker_state
            (staged_proof_transcript data) in
          Some (witness_result, witness_state) \<in>
            set_dist (execute verify_monad s) \<and>
          verifier_header_transcript s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)
            rest \<and>
          ((\<exists>opn \<in> set trace_openings.
            hash_map_new_output_hit
              (merkle_path_target_roots witness_state
                (staged_trace_root data)
                (scale * clength)
                (opening_index opn)
                (opening_value opn)
                (opening_path opn))
              s witness_state) \<or>
           (\<exists>opn \<in> set composition_openings.
            hash_map_new_output_hit
              (merkle_path_target_roots witness_state
                (hd (staged_composition_fri_roots data))
                (scale * clength)
                (opening_index opn)
                (opening_value opn)
                (opening_path opn))
              s witness_state))))"

definition checked_staged_security_with_query_prefix_header_witness_transcript_hit
where
  "checked_staged_security_with_query_prefix_header_witness_transcript_hit
      E out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        E out \<and>
        (\<exists>witness_result witness_state.
          let s = verifier_state_from_adversary attacker_state
            (staged_proof_transcript data) in
          Some (witness_result, witness_state) \<in>
            set_dist (execute verify_monad s) \<and>
          (hash_map_output_values s \<inter>
            set (staged_proof_transcript data) \<noteq> {} \<or>
           hash_map_new_output_hit (set (staged_proof_transcript data))
            s witness_state)))"

definition checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
where
  "checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
      E out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        E out \<and>
        hash_map_output_values
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) \<inter>
          set (staged_proof_transcript data) \<noteq> {})"

definition checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
where
  "checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
      E out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        E out \<and>
        (\<exists>witness_result witness_state.
          let s = verifier_state_from_adversary attacker_state
            (staged_proof_transcript data) in
          Some (witness_result, witness_state) \<in>
            set_dist (execute verify_monad s) \<and>
          hash_map_new_output_hit (set (staged_proof_transcript data))
            s witness_state))"

lemma checked_staged_security_with_query_prefix_header_witness_transcript_hit_imp_pre_or_new:
  assumes hit:
    "checked_staged_security_with_query_prefix_header_witness_transcript_hit
      E out"
  shows
    "checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
        E out \<or>
     checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
        E out"
  using hit
  unfolding
    checked_staged_security_with_query_prefix_header_witness_transcript_hit_def
    checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit_def
    checked_staged_security_with_query_prefix_header_witness_transcript_new_hit_def
  by (cases out) (fastforce split: prod.splits)+

lemma checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit_imp_data_state_pre_hit:
  assumes hit:
    "checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
      E
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
  shows
    "staged_security_with_data_state_transcript_pre_hit
      (Some (((data, attacker_state), result), final_state))"
  using hit
  unfolding
    checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit_def
    staged_security_with_data_state_transcript_pre_hit_def
  by simp

lemma checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit_bound_from_data_state_pre_hit:
  assumes i_bound: "i < rounds"
    and pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
        E)
      adversary_initial_state \<le> P"
proof -
  have projection:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_pre_hit
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out. case out of
        None \<Rightarrow> staged_security_with_data_state_transcript_pre_hit None
      | Some (packed, t) \<Rightarrow>
          staged_security_with_data_state_transcript_pre_hit
            (Some (snd packed, t)))
      adversary_initial_state"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_projection_event
        [OF i_bound])
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
        E)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out. case out of
        None \<Rightarrow> staged_security_with_data_state_transcript_pre_hit None
      | Some (packed, t) \<Rightarrow>
          staged_security_with_data_state_transcript_pre_hit
            (Some (snd packed, t)))
      adversary_initial_state"
  proof (rule wp_event_mono)
    fix out
    assume hit:
      "checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
        E out"
    show
      "(case out of
        None \<Rightarrow> staged_security_with_data_state_transcript_pre_hit None
      | Some (packed, t) \<Rightarrow>
          staged_security_with_data_state_transcript_pre_hit
            (Some (snd packed, t)))"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
          "out =
            Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      show ?thesis
        using
          checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit_imp_data_state_pre_hit
            [OF hit[unfolded out_eq]]
        unfolding out_eq by simp
    qed
  qed
  show ?thesis
    by (rule order_trans[OF event_le])
      (use pre_bound projection in simp)
qed

lemma checked_staged_security_with_query_prefix_header_witness_path_output_hitE:
  assumes hit:
    "checked_staged_security_with_query_prefix_header_witness_path_output_hit
      E trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    and that:
      "\<And>witness_result witness_state rest.
        E (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state)) \<Longrightarrow>
        staged_composition_fri_roots data \<noteq> [] \<Longrightarrow>
        Some (witness_result, witness_state) \<in>
          set_dist
            (execute verify_monad
              (verifier_state_from_adversary attacker_state
                (staged_proof_transcript data))) \<Longrightarrow>
        verifier_header_transcript
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)
          rest \<Longrightarrow>
        ((\<exists>opn \<in> set trace_openings.
            hash_map_new_output_hit
              (merkle_path_target_roots witness_state
                (staged_trace_root data)
                (scale * clength)
                (opening_index opn)
                (opening_value opn)
                (opening_path opn))
              (verifier_state_from_adversary attacker_state
                (staged_proof_transcript data))
              witness_state) \<or>
          (\<exists>opn \<in> set composition_openings.
            hash_map_new_output_hit
              (merkle_path_target_roots witness_state
                (hd (staged_composition_fri_roots data))
                (scale * clength)
                (opening_index opn)
                (opening_value opn)
                (opening_path opn))
              (verifier_state_from_adversary attacker_state
                (staged_proof_transcript data))
              witness_state)) \<Longrightarrow>
        thesis"
  shows thesis
proof -
  have E:
    "E (Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state))"
    and nonempty:
    "staged_composition_fri_roots data \<noteq> []"
    using hit
    unfolding checked_staged_security_with_query_prefix_header_witness_path_output_hit_def
    by simp_all
  from hit obtain witness_result witness_state rest where
    witness:
      "Some (witness_result, witness_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and header:
      "verifier_header_transcript
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        rest"
    and path_hit:
      "((\<exists>opn \<in> set trace_openings.
          hash_map_new_output_hit
            (merkle_path_target_roots witness_state
              (staged_trace_root data)
              (scale * clength)
              (opening_index opn)
              (opening_value opn)
              (opening_path opn))
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            witness_state) \<or>
        (\<exists>opn \<in> set composition_openings.
          hash_map_new_output_hit
            (merkle_path_target_roots witness_state
              (hd (staged_composition_fri_roots data))
              (scale * clength)
              (opening_index opn)
              (opening_value opn)
              (opening_path opn))
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            witness_state))"
    unfolding checked_staged_security_with_query_prefix_header_witness_path_output_hit_def
    by (auto simp: Let_def; blast)
  show ?thesis
    by (rule that[OF E nonempty witness header path_hit])
qed

lemma checked_staged_security_with_query_prefix_header_witness_path_output_imp_transcript_hit:
  assumes hit:
    "checked_staged_security_with_query_prefix_header_witness_path_output_hit
      E trace_openings composition_openings i out"
  shows
    "checked_staged_security_with_query_prefix_header_witness_transcript_hit
      E out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding checked_staged_security_with_query_prefix_header_witness_path_output_hit_def
      checked_staged_security_with_query_prefix_header_witness_transcript_hit_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state data attacker_state result
      final_state where out_eq:
      "out =
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state)"
    by (cases packed) (auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from hit[unfolded out_eq]
  obtain witness_result witness_state rest where
    E:
      "E (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    and witness:
      "Some (witness_result, witness_state) \<in>
        set_dist (execute verify_monad ?s)"
    by (rule
        checked_staged_security_with_query_prefix_header_witness_path_output_hitE)
  have tr_eq: "PTranscript ?s = staged_proof_transcript data"
    by simp
  have transcript_hit:
    "hash_map_output_values ?s \<inter> set (staged_proof_transcript data)
        \<noteq> {} \<or>
     hash_map_new_output_hit (set (staged_proof_transcript data))
        ?s witness_state"
    by (rule verify_monad_trace_root_target_preexisting_or_new
        [OF witness tr_eq])
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_query_prefix_header_witness_transcript_hit_def
    using E witness transcript_hit by (auto simp: Let_def)
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_imp_header:
  assumes hit:
    "checked_staged_security_with_query_prefix_fixed_header_component
      E trace_openings composition_openings i out"
  shows
    "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i out"
  using hit
  unfolding checked_staged_security_with_query_prefix_fixed_header_component_def
  by simp

lemma checked_staged_security_with_query_prefix_fixed_current_authenticated_component_imp_current:
  assumes hit:
    "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
      E trace_openings composition_openings i out"
  shows
    "checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_openings composition_openings i out"
  using hit
  unfolding
    checked_staged_security_with_query_prefix_fixed_current_authenticated_component_def
  by simp

lemma checked_staged_security_with_query_prefix_fixed_header_component_split_current:
  assumes hit:
    "checked_staged_security_with_query_prefix_fixed_header_component
      E trace_openings composition_openings i out"
  shows
    "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
      E trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_header_witness_not_current
      E trace_openings composition_openings i out"
  using hit
  unfolding
    checked_staged_security_with_query_prefix_fixed_current_authenticated_component_def
    checked_staged_security_with_query_prefix_header_witness_not_current_def
  by blast

lemma checked_staged_security_with_query_prefix_fixed_header_componentE:
  assumes hit:
    "checked_staged_security_with_query_prefix_fixed_header_component
      E trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
  obtains
    "E (Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state))"
    "staged_composition_fri_roots data \<noteq> []"
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
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state"
proof -
  have E:
    "E (Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state))"
    and header:
    "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    using hit
    unfolding checked_staged_security_with_query_prefix_fixed_header_component_def
    by simp_all
  from header show ?thesis
  proof (rule
      checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hitE)
    assume comp_nonempty:
      "staged_composition_fri_roots data \<noteq> []"
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
      and target:
      "index (to_nat raw) \<in>
        staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i prefix prefix_state"
    show ?thesis
	      by (rule that[OF E comp_nonempty witness target])
	  qed
	qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_supportE:
  assumes support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  obtains
    "E (Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state))"
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute
          (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive_with_verifier A i
            ((prefix, prefix_state), raw))
          raw_state)"
    "staged_alphas data = sqp_alphas prefix"
    "staged_trace_root data = sqp_trace_root prefix"
    "staged_composition_fri_roots data = sqp_composition_fri_roots prefix"
    "staged_composition_fri_roots data \<noteq> []"
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
    "index (to_nat raw) \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i prefix prefix_state"
proof -
  have prefix_receive:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute
          (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    and continuation:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive_with_verifier A i
            ((prefix, prefix_state), raw))
          raw_state)"
    using support
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
    by (auto elim!: set_dist_bindE)
  have E:
    "E (Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state))"
    and header:
    "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    using hit
    unfolding checked_staged_security_with_query_prefix_fixed_header_component_def
    by simp_all
  from header show ?thesis
  proof (rule
      checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hitE)
    assume comp_nonempty:
      "staged_composition_fri_roots data \<noteq> []"
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
      and target:
      "index (to_nat raw) \<in>
        staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i prefix prefix_state"
    have alphas:
      "staged_alphas data = sqp_alphas prefix"
      by (rule checked_staged_security_with_query_prefix_data_state_alphas_eq)
        (rule support)
    have trace_root:
      "staged_trace_root data = sqp_trace_root prefix"
      and comp_roots:
      "staged_composition_fri_roots data = sqp_composition_fri_roots prefix"
      using support
      unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
        checked_staged_after_query_prefix_receive_with_verifier_def
        checked_staged_after_query_prefix_receive_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    show ?thesis
    by (rule that[OF E prefix_receive continuation alphas trace_root
          comp_roots comp_nonempty witness target])
  qed
qed

lemma checked_staged_security_with_query_prefix_header_witness_not_current_imp_path_output_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_header_witness_not_current
        E trace_openings composition_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "checked_staged_security_with_query_prefix_header_witness_path_output_hit
      E trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  let ?out =
    "Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have fixed:
    "checked_staged_security_with_query_prefix_fixed_header_component
      E trace_openings composition_openings i ?out"
    and not_current:
    "\<not> checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_openings composition_openings i ?out"
    using hit
    unfolding
      checked_staged_security_with_query_prefix_header_witness_not_current_def
    by simp_all
  have support_facts:
    "E ?out \<and>
     Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive_with_verifier A i
              ((prefix, prefix_state), raw))
            raw_state) \<and>
     staged_alphas data = sqp_alphas prefix \<and>
     staged_composition_fri_roots data \<noteq> [] \<and>
     (trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<and>
     index (to_nat raw) \<in>
        staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i prefix prefix_state"
  proof (rule
      checked_staged_security_with_query_prefix_fixed_header_component_supportE
      [OF support fixed])
    assume E: "E ?out"
      and continuation:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive_with_verifier A i
              ((prefix, prefix_state), raw))
            raw_state)"
      and alphas_eq: "staged_alphas data = sqp_alphas prefix"
      and comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
      and witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
      and target:
      "index (to_nat raw) \<in>
        staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i prefix prefix_state"
    show ?thesis
      using E continuation alphas_eq comp_nonempty witness target by simp
  qed
  have E: "E ?out"
    using support_facts by blast
  have continuation:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive_with_verifier A i
              ((prefix, prefix_state), raw))
            raw_state)"
    using support_facts by blast
  have alphas_eq: "staged_alphas data = sqp_alphas prefix"
    using support_facts by blast
  have comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
    using support_facts by blast
  have witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
    using support_facts by blast
  have target:
      "index (to_nat raw) \<in>
        staged_query_prefix_candidate_opening_query_target_from_prefix
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          i prefix prefix_state"
    using support_facts by blast
  from checked_staged_after_query_prefix_receive_with_verifier_outcome(2)
      [OF continuation]
  have current_verifier:
    "Some (result, final_state) \<in>
      set_dist (execute verify_monad ?s)"
    .
  have s_ext_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF current_verifier])
  from witness obtain witness_result witness_state rest where
    witness_out:
      "Some (witness_result, witness_state) \<in>
        set_dist (execute verify_monad ?s)"
    and trace_table_witness:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings witness_state"
    and comp_table_witness:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings witness_state"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        rest"
    by (rule query_header_supported_partial_opening_witnessesE)
  have s_ext_witness: "?s \<le> witness_state"
    by (rule verify_monad_hash_extends[OF witness_out])
  have consistent:
    "partial_query_openings_consistent trace_openings composition_openings
      (staged_alphas data) (index (to_nat raw))"
  proof -
    have target_success:
      "index (to_nat raw) \<in>
        partial_query_success_indices_at
          ((replicate rounds []) [i := trace_openings])
          ((replicate rounds []) [i := composition_openings])
          (sqp_alphas prefix) i"
      using target
      unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
      by simp
    then have round:
      "partial_query_round_consistent
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        (sqp_alphas prefix) i (index (to_nat raw))"
      unfolding partial_query_success_indices_at_def by simp
    have trace_nth:
      "((replicate rounds []) [i := trace_openings]) ! i = trace_openings"
      using i_bound by simp
    have comp_nth:
      "((replicate rounds []) [i := composition_openings]) ! i =
        composition_openings"
      using i_bound by simp
    have idx_sample: "index (to_nat raw) \<in> query_sample_space"
      using round unfolding partial_query_round_consistent_def by simp
    have trace_indices_full:
        "map opening_index
          (((replicate rounds []) [i := trace_openings]) ! i) =
          powers_scaled (index (to_nat raw))"
      using round unfolding partial_query_round_consistent_def by blast
    have comp_indices_full:
        "map opening_index
          (((replicate rounds []) [i := composition_openings]) ! i) =
          [index (to_nat raw),
           fri_sibling_index (scale * clength) (index (to_nat raw))]"
      using round unfolding partial_query_round_consistent_def by blast
    have comp_nonempty_full:
        "((replicate rounds []) [i := composition_openings]) ! i \<noteq> []"
      using round unfolding partial_query_round_consistent_def by blast
    have comp_value_full:
        "opening_value
          (((replicate rounds []) [i := composition_openings]) ! i ! 0) =
          cp_eval (sqp_alphas prefix)
            (map opening_value
              (((replicate rounds []) [i := trace_openings]) ! i))
            (h ^ index (to_nat raw) * shift)"
      using round unfolding partial_query_round_consistent_def by blast
    have
      "partial_query_openings_consistent trace_openings composition_openings
        (sqp_alphas prefix) (index (to_nat raw))"
      unfolding partial_query_openings_consistent_def
      using idx_sample trace_indices_full comp_indices_full comp_nonempty_full
        comp_value_full trace_nth comp_nth
      by simp
    then show ?thesis
      using alphas_eq by simp
  qed
  have trace_pullback:
    "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings ?s \<or>
     (\<exists>opn \<in> set trace_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots witness_state
          (staged_trace_root data)
          (scale * clength)
          (opening_index opn)
          (opening_value opn)
          (opening_path opn)) ?s witness_state)"
    by (rule partial_authenticated_table_pullback_or_new_output_hit
        [OF s_ext_witness trace_table_witness])
  then show ?thesis
  proof
    assume trace_table_s:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings ?s"
    have comp_pullback:
      "partial_authenticated_table (hd (staged_composition_fri_roots data))
          (scale * clength) composition_openings ?s \<or>
       (\<exists>opn \<in> set composition_openings.
        hash_map_new_output_hit
          (merkle_path_target_roots witness_state
            (hd (staged_composition_fri_roots data))
            (scale * clength)
            (opening_index opn)
            (opening_value opn)
            (opening_path opn)) ?s witness_state)"
      by (rule partial_authenticated_table_pullback_or_new_output_hit
          [OF s_ext_witness comp_table_witness])
    then show ?thesis
    proof
      assume comp_table_s:
        "partial_authenticated_table
          (hd (staged_composition_fri_roots data))
          (scale * clength) composition_openings ?s"
      have trace_table_final:
        "partial_authenticated_table (staged_trace_root data)
          (scale * clength) trace_openings final_state"
        by (rule partial_authenticated_table_mono[OF trace_table_s s_ext_final])
      have comp_table_final:
        "partial_authenticated_table
          (hd (staged_composition_fri_roots data))
          (scale * clength) composition_openings final_state"
        by (rule partial_authenticated_table_mono[OF comp_table_s s_ext_final])
      have current:
        "checked_staged_security_with_query_prefix_authenticated_opening_hit
          trace_openings composition_openings i ?out"
        unfolding
          checked_staged_security_with_query_prefix_authenticated_opening_hit_def
        using comp_nonempty trace_table_final comp_table_final consistent
        by simp
      then show ?thesis
        using not_current by contradiction
    next
      assume comp_path:
        "\<exists>opn\<in>set composition_openings.
          hash_map_new_output_hit
            (merkle_path_target_roots witness_state
              (hd (staged_composition_fri_roots data)) (scale * clength)
              (opening_index opn) (opening_value opn) (opening_path opn))
            ?s witness_state"
      have body:
        "\<exists>witness_result witness_state rest.
          let s = ?s in
          Some (witness_result, witness_state) \<in>
            set_dist (execute verify_monad s) \<and>
          verifier_header_transcript s
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)
            rest \<and>
          ((\<exists>opn \<in> set trace_openings.
            hash_map_new_output_hit
              (merkle_path_target_roots witness_state
                (staged_trace_root data)
                (scale * clength)
                (opening_index opn)
                (opening_value opn)
                (opening_path opn))
              s witness_state) \<or>
           (\<exists>opn \<in> set composition_openings.
            hash_map_new_output_hit
              (merkle_path_target_roots witness_state
                (hd (staged_composition_fri_roots data))
                (scale * clength)
                (opening_index opn)
                (opening_value opn)
                (opening_path opn))
              s witness_state))"
        by (intro exI[of _ witness_result] exI[of _ witness_state]
            exI[of _ rest])
          (simp add: witness_out header comp_path)
      show ?thesis
        unfolding
          checked_staged_security_with_query_prefix_header_witness_path_output_hit_def
        using E comp_nonempty body by simp
    qed
  next
    assume trace_path:
      "\<exists>opn\<in>set trace_openings.
        hash_map_new_output_hit
          (merkle_path_target_roots witness_state
            (staged_trace_root data) (scale * clength)
            (opening_index opn) (opening_value opn) (opening_path opn))
          ?s witness_state"
    have body:
      "\<exists>witness_result witness_state rest.
        let s = ?s in
        Some (witness_result, witness_state) \<in>
          set_dist (execute verify_monad s) \<and>
        verifier_header_transcript s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)
          rest \<and>
        ((\<exists>opn \<in> set trace_openings.
          hash_map_new_output_hit
            (merkle_path_target_roots witness_state
              (staged_trace_root data)
              (scale * clength)
              (opening_index opn)
              (opening_value opn)
              (opening_path opn))
            s witness_state) \<or>
         (\<exists>opn \<in> set composition_openings.
          hash_map_new_output_hit
            (merkle_path_target_roots witness_state
              (hd (staged_composition_fri_roots data))
              (scale * clength)
              (opening_index opn)
              (opening_value opn)
              (opening_path opn))
            s witness_state))"
      by (intro exI[of _ witness_result] exI[of _ witness_state]
          exI[of _ rest])
        (simp add: witness_out header trace_path)
    show ?thesis
      unfolding
        checked_staged_security_with_query_prefix_header_witness_path_output_hit_def
      using E comp_nonempty body by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_fixed_current_authenticated_component_imp_prefix_or_path_output_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i out"
  shows
    "checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings out"
  by (rule
      checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_prefix_or_path_output_hit_on_support
      [OF wf controlled i_bound support])
    (rule
      checked_staged_security_with_query_prefix_fixed_current_authenticated_component_imp_current
      [OF hit])

lemma checked_staged_security_with_query_prefix_fixed_header_component_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i)
      adversary_initial_state"
  proof (rule wp_event_mono)
    fix out
    assume
      "checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i out"
    then have
      "checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
        trace_openings composition_openings i out"
      by (rule
          checked_staged_security_with_query_prefix_fixed_header_component_imp_header)
    then show
      "checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i out"
      by (rule
          checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_imp_actual)
  qed
  have actual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
    by (rule checked_staged_security_with_actual_query_prefix_candidate_opening_hit_bound
        [OF raw_bound wf controlled])
      (use i_bound in simp)
  show ?thesis
    by (rule order_trans[OF event_le actual_bound])
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_bound
        [OF raw_bound wf controlled i_bound])
qed

lemma checked_staged_security_with_query_prefix_fixed_current_authenticated_component_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_query_prefix_fixed_current_authenticated_component_imp_current)
  have current_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
    by (rule checked_staged_security_with_query_prefix_authenticated_opening_hit_bound
        [OF raw_bound wf controlled i_bound])
  show ?thesis
    by (rule order_trans[OF event_le current_bound])
qed

lemma checked_staged_security_with_query_prefix_fixed_current_authenticated_component_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_fixed_current_authenticated_component_bound
        [OF raw_bound wf controlled i_bound])
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_imp_current_or_witness_path_output_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i out"
  shows
    "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_header_witness_path_output_hit
        E trace_openings composition_openings i out"
proof (cases out)
  case None
  then have False
    using hit
    unfolding
      checked_staged_security_with_query_prefix_fixed_header_component_def
      checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_def
    by simp
  then show ?thesis by simp
next
  case (Some packed)
  obtain prefix prefix_state raw raw_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state)"
    using Some by (cases packed) (auto split: prod.splits)
  from checked_staged_security_with_query_prefix_fixed_header_component_split_current
      [OF hit]
  show ?thesis
  proof
    assume current:
      "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i out"
    then show ?thesis by simp
  next
    assume not_current:
      "checked_staged_security_with_query_prefix_header_witness_not_current
        E trace_openings composition_openings i out"
    have support':
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
      using support out_eq by simp
    have not_current':
      "checked_staged_security_with_query_prefix_header_witness_not_current
        E trace_openings composition_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      using not_current out_eq by simp
    have path:
      "checked_staged_security_with_query_prefix_header_witness_path_output_hit
        E trace_openings composition_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      by (rule
          checked_staged_security_with_query_prefix_header_witness_not_current_imp_path_output_on_support
          [OF wf controlled i_bound support' not_current'])
    then show ?thesis
      using out_eq by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_bound_from_current_and_witness_path_output:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and current_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
          E trace_openings composition_openings i)
        adversary_initial_state \<le> P"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_path_output_hit
          E trace_openings composition_openings i)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le> P + Q"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out.
        checked_staged_security_with_query_prefix_fixed_current_authenticated_component
          E trace_openings composition_openings i out \<or>
        checked_staged_security_with_query_prefix_header_witness_path_output_hit
          E trace_openings composition_openings i out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_fixed_header_component_imp_current_or_witness_path_output_on_support
        [OF wf controlled i_bound])
  have union_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out.
        checked_staged_security_with_query_prefix_fixed_current_authenticated_component
          E trace_openings composition_openings i out \<or>
        checked_staged_security_with_query_prefix_header_witness_path_output_hit
          E trace_openings composition_openings i out)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i)
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_witness_path_output_hit
        E trace_openings composition_openings i)
      adversary_initial_state"
    by (rule wp_event_union_bound)
  have sum_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i)
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_witness_path_output_hit
        E trace_openings composition_openings i)
      adversary_initial_state \<le> P + Q"
    by (intro add_mono current_bound path_bound)
  show ?thesis
    by (rule order_trans[OF event_le])
      (rule order_trans[OF union_bound sum_bound])
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_imp_current_or_witness_transcript_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i out"
  shows
    "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_header_witness_transcript_hit
        E out"
proof -
  have split:
    "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_header_witness_path_output_hit
        E trace_openings composition_openings i out"
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_imp_current_or_witness_path_output_on_support
        [OF wf controlled i_bound support hit])
  then show ?thesis
  proof
    assume
      "checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i out"
    then show ?thesis by simp
  next
    assume path:
      "checked_staged_security_with_query_prefix_header_witness_path_output_hit
        E trace_openings composition_openings i out"
    have
      "checked_staged_security_with_query_prefix_header_witness_transcript_hit
        E out"
      by (rule
          checked_staged_security_with_query_prefix_header_witness_path_output_imp_transcript_hit
          [OF path])
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_bound_from_current_and_witness_transcript_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and current_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
          E trace_openings composition_openings i)
        adversary_initial_state \<le> P"
    and transcript_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_hit
          E)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le> P + Q"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out.
        checked_staged_security_with_query_prefix_fixed_current_authenticated_component
          E trace_openings composition_openings i out \<or>
        checked_staged_security_with_query_prefix_header_witness_transcript_hit
          E out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_fixed_header_component_imp_current_or_witness_transcript_hit_on_support
        [OF wf controlled i_bound])
  have union_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out.
        checked_staged_security_with_query_prefix_fixed_current_authenticated_component
          E trace_openings composition_openings i out \<or>
        checked_staged_security_with_query_prefix_header_witness_transcript_hit
          E out)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i)
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_witness_transcript_hit
        E)
      adversary_initial_state"
    by (rule wp_event_union_bound)
  have sum_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i)
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_witness_transcript_hit
        E)
      adversary_initial_state \<le> P + Q"
    by (intro add_mono current_bound transcript_bound)
  show ?thesis
    by (rule order_trans[OF event_le])
      (rule order_trans[OF union_bound sum_bound])
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_bound_from_current_pre_and_witness_new_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and current_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
          E trace_openings composition_openings i)
        adversary_initial_state \<le> P"
    and pre_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
          E)
        adversary_initial_state \<le> R"
    and new_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
          E)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le> P + R + Q"
proof -
  have transcript_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_witness_transcript_hit
        E)
      adversary_initial_state \<le> R + Q"
  proof -
    have event_le:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_hit
          E)
        adversary_initial_state \<le>
       wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (\<lambda>out.
          checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
            E out \<or>
          checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
            E out)
        adversary_initial_state"
      by (rule wp_event_mono)
        (rule
          checked_staged_security_with_query_prefix_header_witness_transcript_hit_imp_pre_or_new)
    have union_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (\<lambda>out.
          checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
            E out \<or>
          checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
            E out)
        adversary_initial_state \<le>
       wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
          E)
        adversary_initial_state +
       wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
          E)
        adversary_initial_state"
      by (rule wp_event_union_bound)
    have sum_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
          E)
        adversary_initial_state +
       wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
          E)
        adversary_initial_state \<le> R + Q"
      by (intro add_mono pre_bound new_bound)
    show ?thesis
      by (rule order_trans[OF event_le])
        (rule order_trans[OF union_bound sum_bound])
  qed
  have header_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le> P + (R + Q)"
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_bound_from_current_and_witness_transcript_hit
        [OF wf controlled i_bound current_bound transcript_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_bound_from_witness_path_output:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_path_output_hit
          E trace_openings composition_openings i)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space) + Q"
proof -
  have current_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
    by (rule
        checked_staged_security_with_query_prefix_fixed_current_authenticated_component_bound
        [OF raw_bound wf controlled i_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_bound_from_current_and_witness_path_output
        [OF wf controlled i_bound current_bound path_bound])
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_bound_from_witness_path_output_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_path_output_hit
          E trace_openings composition_openings i)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space) + Q"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_bound_from_witness_path_output
        [OF raw_bound wf controlled i_bound path_bound])
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_bound_from_witness_transcript_hit:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and transcript_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_hit
          E)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space) + Q"
proof -
  have current_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
    by (rule
        checked_staged_security_with_query_prefix_fixed_current_authenticated_component_bound
        [OF raw_bound wf controlled i_bound])
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_bound_from_current_and_witness_transcript_hit
        [OF wf controlled i_bound current_bound transcript_bound])
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_bound_from_witness_transcript_hit_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and transcript_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_hit
          E)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space) + Q"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_bound_from_witness_transcript_hit
        [OF raw_bound wf controlled i_bound transcript_bound])
qed

lemma checked_staged_security_with_query_prefix_fixed_header_component_bound_from_data_state_pre_and_witness_new_hit:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> R"
    and new_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_transcript_new_hit
          E)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space) + R + Q"
proof -
  have current_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_current_authenticated_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
    by (rule
        checked_staged_security_with_query_prefix_fixed_current_authenticated_component_bound
        [OF raw_bound wf controlled i_bound])
  have pre_hit_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit
        E)
      adversary_initial_state \<le> R"
    by (rule
        checked_staged_security_with_query_prefix_header_witness_transcript_pre_hit_bound_from_data_state_pre_hit
        [OF i_bound pre_bound])
  have header_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        E trace_openings composition_openings i)
      adversary_initial_state \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
       (1::prob) / nnreal (card query_sample_space)) + R + Q"
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_bound_from_current_pre_and_witness_new_hit
        [OF wf controlled i_bound current_bound pre_hit_bound new_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_data_state_bound_by_query_prefix_fixed_header_component:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and event_imp:
      "\<And>out.
        (case out of
          None \<Rightarrow> E None
        | Some (packed, t) \<Rightarrow> E (Some (snd packed, t))) \<Longrightarrow>
        checked_staged_security_with_query_prefix_fixed_header_component
          C trace_openings composition_openings i out"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A) E
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
proof -
  have projection:
    "wp_event (checked_staged_security_experiment_with_data_state A) E
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out. case out of
        None \<Rightarrow> E None
      | Some (packed, t) \<Rightarrow> E (Some (snd packed, t)))
      adversary_initial_state"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_projection_event
        [OF i_bound])
  have lifted_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out. case out of
        None \<Rightarrow> E None
      | Some (packed, t) \<Rightarrow> E (Some (snd packed, t)))
      adversary_initial_state \<le>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_fixed_header_component
          C trace_openings composition_openings i)
        adversary_initial_state"
    by (rule wp_event_mono) (use event_imp in blast)
  have fixed_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        C trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
    by (rule checked_staged_security_with_query_prefix_fixed_header_component_bound
        [OF raw_bound wf controlled i_bound])
  show ?thesis
    unfolding projection
    by (rule order_trans[OF lifted_bound fixed_bound])
qed

lemma checked_staged_security_with_data_state_bound_by_query_prefix_fixed_header_component_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and event_imp:
      "\<And>out.
        (case out of
          None \<Rightarrow> E None
        | Some (packed, t) \<Rightarrow> E (Some (snd packed, t))) \<Longrightarrow>
        checked_staged_security_with_query_prefix_fixed_header_component
          C trace_openings composition_openings i out"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A) E
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_bound_by_query_prefix_fixed_header_component
        [OF raw_bound wf controlled i_bound event_imp])
qed

lemma checked_staged_security_with_data_state_bound_by_query_prefix_fixed_header_component_from_witness_path_output:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_path_output_hit
          C trace_openings composition_openings i)
        adversary_initial_state \<le> Q"
    and event_imp:
      "\<And>out.
        (case out of
          None \<Rightarrow> E None
        | Some (packed, t) \<Rightarrow> E (Some (snd packed, t))) \<Longrightarrow>
        checked_staged_security_with_query_prefix_fixed_header_component
          C trace_openings composition_openings i out"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A) E
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space) + Q"
proof -
  have projection:
    "wp_event (checked_staged_security_experiment_with_data_state A) E
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out. case out of
        None \<Rightarrow> E None
      | Some (packed, t) \<Rightarrow> E (Some (snd packed, t)))
      adversary_initial_state"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_projection_event
        [OF i_bound])
  have lifted_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out. case out of
        None \<Rightarrow> E None
      | Some (packed, t) \<Rightarrow> E (Some (snd packed, t)))
      adversary_initial_state \<le>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_fixed_header_component
          C trace_openings composition_openings i)
        adversary_initial_state"
    by (rule wp_event_mono) (use event_imp in blast)
  have fixed_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_fixed_header_component
        C trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space) + Q"
    by (rule
        checked_staged_security_with_query_prefix_fixed_header_component_bound_from_witness_path_output
        [OF raw_bound wf controlled i_bound path_bound])
  show ?thesis
    unfolding projection
    by (rule order_trans[OF lifted_bound fixed_bound])
qed

lemma checked_staged_security_with_data_state_bound_by_query_prefix_fixed_header_component_from_witness_path_output_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_path_output_hit
          C trace_openings composition_openings i)
        adversary_initial_state \<le> Q"
    and event_imp:
      "\<And>out.
        (case out of
          None \<Rightarrow> E None
        | Some (packed, t) \<Rightarrow> E (Some (snd packed, t))) \<Longrightarrow>
        checked_staged_security_with_query_prefix_fixed_header_component
          C trace_openings composition_openings i out"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A) E
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space) + Q"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_bound_by_query_prefix_fixed_header_component_from_witness_path_output
        [OF raw_bound wf controlled i_bound path_bound event_imp])
qed

lemma checked_staged_security_with_actual_alpha_prefix_data_state_bound_by_query_prefix_fixed_header_component:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and event_imp:
      "\<And>out.
        (case out of
          None \<Rightarrow> D None
        | Some (packed, t) \<Rightarrow> D (Some (snd packed, t))) \<Longrightarrow>
        checked_staged_security_with_query_prefix_fixed_header_component
          C trace_openings composition_openings i out"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. case out of
        None \<Rightarrow> D None
      | Some (packed, t) \<Rightarrow>
          D (Some (((snd (fst (fst packed)), snd (fst packed)), snd packed),
            t)))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. case out of
        None \<Rightarrow> D None
      | Some (packed, t) \<Rightarrow> D (Some (?project packed, t)))
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      D
      adversary_initial_state"
  proof -
    have
      "wp_event (checked_staged_security_experiment_with_data_state A)
        D adversary_initial_state =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
          \<bind> (\<lambda>x. return (?project x)))
        D adversary_initial_state"
      using
        checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
        [of A]
      by simp
    also have "... =
      wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        (\<lambda>out. case out of
          None \<Rightarrow> D None
        | Some (packed, t) \<Rightarrow> D (Some (?project packed, t)))
        adversary_initial_state"
      by (rule wp_event_bind_return_map)
    finally show ?thesis
      by simp
  qed
  have data_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      D adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
    by (rule
        checked_staged_security_with_data_state_bound_by_query_prefix_fixed_header_component
        [OF raw_bound wf controlled i_bound event_imp])
  show ?thesis
    unfolding projection
    by (rule data_bound)
qed

lemma checked_staged_security_with_actual_alpha_prefix_data_state_bound_by_query_prefix_fixed_header_component_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and event_imp:
      "\<And>out.
        (case out of
          None \<Rightarrow> D None
        | Some (packed, t) \<Rightarrow> D (Some (snd packed, t))) \<Longrightarrow>
        checked_staged_security_with_query_prefix_fixed_header_component
          C trace_openings composition_openings i out"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. case out of
        None \<Rightarrow> D None
      | Some (packed, t) \<Rightarrow>
          D (Some (((snd (fst (fst packed)), snd (fst packed)), snd packed),
            t)))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_data_state_bound_by_query_prefix_fixed_header_component
        [OF raw_bound wf controlled i_bound event_imp])
qed

lemma checked_staged_security_with_actual_alpha_prefix_data_state_bound_by_query_prefix_fixed_header_component_from_witness_path_output:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_path_output_hit
          C trace_openings composition_openings i)
        adversary_initial_state \<le> Q"
    and event_imp:
      "\<And>out.
        (case out of
          None \<Rightarrow> D None
        | Some (packed, t) \<Rightarrow> D (Some (snd packed, t))) \<Longrightarrow>
        checked_staged_security_with_query_prefix_fixed_header_component
          C trace_openings composition_openings i out"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. case out of
        None \<Rightarrow> D None
      | Some (packed, t) \<Rightarrow>
          D (Some (((snd (fst (fst packed)), snd (fst packed)), snd packed),
            t)))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space) + Q"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. case out of
        None \<Rightarrow> D None
      | Some (packed, t) \<Rightarrow> D (Some (?project packed, t)))
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      D
      adversary_initial_state"
  proof -
    have
      "wp_event (checked_staged_security_experiment_with_data_state A)
        D adversary_initial_state =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
          \<bind> (\<lambda>x. return (?project x)))
        D adversary_initial_state"
      using
        checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
        [of A]
      by simp
    also have "... =
      wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        (\<lambda>out. case out of
          None \<Rightarrow> D None
        | Some (packed, t) \<Rightarrow> D (Some (?project packed, t)))
        adversary_initial_state"
      by (rule wp_event_bind_return_map)
    finally show ?thesis
      by simp
  qed
  have data_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      D adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space) + Q"
    by (rule
        checked_staged_security_with_data_state_bound_by_query_prefix_fixed_header_component_from_witness_path_output
        [OF raw_bound wf controlled i_bound path_bound event_imp])
  show ?thesis
    unfolding projection
    by (rule data_bound)
qed

lemma checked_staged_security_with_actual_alpha_prefix_data_state_bound_by_query_prefix_fixed_header_component_from_witness_path_output_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_header_witness_path_output_hit
          C trace_openings composition_openings i)
        adversary_initial_state \<le> Q"
    and event_imp:
      "\<And>out.
        (case out of
          None \<Rightarrow> D None
        | Some (packed, t) \<Rightarrow> D (Some (snd packed, t))) \<Longrightarrow>
        checked_staged_security_with_query_prefix_fixed_header_component
          C trace_openings composition_openings i out"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (\<lambda>out. case out of
        None \<Rightarrow> D None
      | Some (packed, t) \<Rightarrow>
          D (Some (((snd (fst (fst packed)), snd (fst packed)), snd packed),
            t)))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space) + Q"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_data_state_bound_by_query_prefix_fixed_header_component_from_witness_path_output
        [OF raw_bound wf controlled i_bound path_bound event_imp])
qed

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_bound:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_imp_actual)
  have actual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_actual_query_prefix_candidate_opening_hit
        ((replicate rounds []) [i := trace_openings])
        ((replicate rounds []) [i := composition_openings])
        i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
    by (rule checked_staged_security_with_actual_query_prefix_candidate_opening_hit_bound
        [OF raw_bound wf controlled])
      (use i_bound in simp)
  show ?thesis
    by (rule order_trans[OF event_le actual_bound])
qed

lemma checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit
        trace_openings composition_openings i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      (1::prob) / nnreal (card query_sample_space)"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_header_authenticated_candidate_opening_hit_bound
        [OF raw_bound wf controlled i_bound])
qed

end

end
