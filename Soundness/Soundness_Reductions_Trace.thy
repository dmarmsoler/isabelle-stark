(*  Title:      Stark/Soundness_Reductions_Trace.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Reductions_Trace
  imports Soundness_Partial_Merkle
begin

text \<open>FRI-table acceptance, transcript-target, and trace-table candidate reductions.\<close>

context soundness
begin

definition accepted_with_fri_tables
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "accepted_with_fri_tables s out \<longleftrightarrow>
      accepted out \<and> fri_merkle_binding_good s out"

lemma accepted_with_fri_tables_imp_accepted:
  assumes "accepted_with_fri_tables s out"
  shows "accepted out"
  using assms unfolding accepted_with_fri_tables_def by simp

lemma accepted_with_fri_tablesE:
  assumes tables: "accepted_with_fri_tables s out"
  obtains trace_table composition_table as query_idxs
      trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final trace_round_layers composition_round_layers
      trace_tables composition_tables trace_final_table composition_final_table
  where
    "accepted_with_bound_tables s out trace_table composition_table as
      query_idxs"
    and "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      query_idxs trace_round_layers composition_round_layers"
    and "trace_fri_tables_bound s out trace_roots trace_bs trace_final
      query_idxs trace_round_layers trace_tables trace_final_table"
    and "composition_fri_tables_bound s out dg composition_roots
      composition_bs composition_final query_idxs composition_round_layers
      composition_tables composition_final_table"
    and "fri_initial_table_agrees trace_table trace_tables"
    and "fri_initial_table_agrees composition_table composition_tables"
  using tables
  unfolding accepted_with_fri_tables_def fri_merkle_binding_good_def
  by (blast intro: that)

lemma accepted_with_fri_tables_obtain_bound_tables:
  assumes "accepted_with_fri_tables s out"
  obtains trace_table composition_table as query_idxs
  where "accepted_with_bound_tables s out trace_table composition_table as
    query_idxs"
  using assms by (elim accepted_with_fri_tablesE) blast

lemma accepted_partition_fri_merkle_binding:
  assumes "accepted out"
  shows "fri_merkle_binding_bad s out \<or> accepted_with_fri_tables s out"
  using assms
  unfolding fri_merkle_binding_bad_def accepted_with_fri_tables_def
  by blast

lemma accepted_with_bound_tables_trace_root_target_hit:
  assumes bound:
      "accepted_with_bound_tables (verifier_initial_state tr)
        (Some (result, final_state)) trace_table composition_table as
        query_idxs"
  shows
    "hash_map_new_output_hit (set tr) (verifier_initial_state tr) final_state"
proof -
  from bound obtain fr f_fri_roots f_final dg composition_fri_roots final rest
    where header:
      "verifier_header_transcript (verifier_initial_state tr) fr f_fri_roots
        f_final as dg composition_fri_roots final rest"
    and bind:
      "merkle_root_binds_table fr trace_table final_state"
    unfolding accepted_with_bound_tables_def by blast
  have table_nonempty: "trace_table \<noteq> []"
    using accepted_with_bound_tables_shapes(1)[OF bound]
      eval_domain_nontrivial by auto
  from merkle_root_binds_nonempty_table_output_lookup[OF bind table_nonempty]
  obtain input where lookup:
    "fmlookup (HashMap final_state) input = Some fr"
    by blast
  have root_in: "fr \<in> set tr"
    using header
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
  have fresh:
    "fmlookup (HashMap (verifier_initial_state tr)) input = None"
    by simp
  show ?thesis
    unfolding hash_map_new_output_hit_def
    using fresh lookup root_in by blast
qed

lemma accepted_with_fri_tables_imp_transcript_target_hit:
  assumes tables:
      "accepted_with_fri_tables (verifier_initial_state tr) out"
  shows
    "hash_new_output_hit_event (set tr) (verifier_initial_state tr) out"
proof -
  from accepted_with_fri_tables_obtain_bound_tables[OF tables]
  obtain trace_table composition_table as query_idxs where bound:
    "accepted_with_bound_tables (verifier_initial_state tr) out trace_table
      composition_table as query_idxs"
    by blast
  from accepted_with_bound_tables_imp_accepted[OF bound]
  obtain result final_state where out_eq: "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  have hit:
    "hash_map_new_output_hit (set tr) (verifier_initial_state tr) final_state"
    by (rule accepted_with_bound_tables_trace_root_target_hit)
      (use bound out_eq in simp)
  show ?thesis
    unfolding hash_new_output_hit_event_def out_eq using hit by simp
qed

lemma accepted_imp_fri_merkle_binding_bad_or_transcript_target_hit:
  assumes acc: "accepted out"
  shows
    "fri_merkle_binding_bad (verifier_initial_state tr) out \<or>
      hash_new_output_hit_event (set tr) (verifier_initial_state tr) out"
proof -
  from accepted_partition_fri_merkle_binding
      [of out "verifier_initial_state tr", OF acc]
  show ?thesis
  proof
    assume "fri_merkle_binding_bad (verifier_initial_state tr) out"
    then show ?thesis by simp
  next
    assume tables:
      "accepted_with_fri_tables (verifier_initial_state tr) out"
    have "hash_new_output_hit_event (set tr) (verifier_initial_state tr) out"
      by (rule accepted_with_fri_tables_imp_transcript_target_hit[OF tables])
    then show ?thesis by simp
  qed
qed

lemma verify_monad_verifier_initial_trace_root_target_hit:
  assumes outcome:
      "Some (result, final_state) \<in>
        set_dist (execute verify_monad (verifier_initial_state tr))"
  shows
    "hash_map_new_output_hit (set tr) (verifier_initial_state tr)
      final_state"
proof -
  let ?s = "verifier_initial_state tr"
  from verify_monad_header_extraction[OF outcome]
  obtain fr f_fl f_final as dg fl final query_state where
    header:
      "verifier_header_transcript ?s fr (map snd f_fl) f_final as dg
        (map snd fl) final (PTranscript query_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    by (rule verify_monad_header_query_extraction[OF outcome])
  obtain query_idxs trace_openings where
    len_query_idxs: "length query_idxs = rounds"
    and len_openings: "length trace_openings = rounds"
    and indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)"
    and tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) final_state"
  proof (rule ntimes_verifier_query_rounds_authenticated_trace_openings_no_raws
      [OF query_out])
    fix query_idxs trace_openings
    assume len_query_idxs: "length query_idxs = rounds"
      and len_openings: "length trace_openings = rounds"
      and indices:
        "\<And>i. i < rounds \<Longrightarrow>
          map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)"
      and tables:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_authenticated_table fr (scale * clength)
            (trace_openings ! i) final_state"
    show ?thesis
      by (rule that[OF len_query_idxs len_openings indices tables])
  qed
  have round0: "0 < rounds"
    by (rule rounds_positive)
  have openings0_nonempty:
    "trace_openings ! 0 \<noteq> []"
  proof -
    have "map opening_index (trace_openings ! 0) =
        powers_scaled (query_idxs ! 0)"
      by (rule indices[OF round0])
    moreover have "powers_scaled (query_idxs ! 0) \<noteq> []"
      using powers_pos unfolding powers_scaled_def by simp
    ultimately show ?thesis
      by auto
  qed
  then obtain opn where opn_in:
    "opn \<in> set (trace_openings ! 0)"
    by (cases "trace_openings ! 0") auto
  have table0:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! 0) final_state"
    using tables[OF round0] by simp
  have opn_root: "opening_root opn = fr"
    using table0 opn_in unfolding partial_authenticated_table_def by blast
  have opn_auth: "authenticated_opening_in final_state opn"
    using table0 opn_in unfolding partial_authenticated_table_def by blast
  from authenticated_opening_root_lookup[OF opn_auth]
  obtain input where lookup:
    "fmlookup (HashMap final_state) input = Some fr"
    using opn_root by auto
  have root_in: "fr \<in> set tr"
    using header
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
  have fresh: "fmlookup (HashMap ?s) input = None"
    by simp
  show ?thesis
    unfolding hash_map_new_output_hit_def
    using fresh lookup root_in by blast
qed

lemma verify_monad_trace_root_target_preexisting_or_new:
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and tr_eq: "PTranscript s = tr"
  shows
    "hash_map_output_values s \<inter> set tr \<noteq> {} \<or>
      hash_map_new_output_hit (set tr) s final_state"
proof -
  from verify_monad_header_extraction[OF outcome]
  obtain fr f_fl f_final as dg fl final query_state where
    header:
      "verifier_header_transcript s fr (map snd f_fl) f_final as dg
        (map snd fl) final (PTranscript query_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    by (rule verify_monad_header_query_extraction[OF outcome])
  obtain query_idxs trace_openings where
    indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs ! i)"
    and tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) final_state"
  proof (rule ntimes_verifier_query_rounds_authenticated_trace_openings_no_raws
      [OF query_out])
    fix query_idxs trace_openings
    assume indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
      and tables:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_authenticated_table fr (scale * clength)
            (trace_openings ! i) final_state"
    show ?thesis
      by (rule that[OF indices tables])
  qed
  have round0: "0 < rounds"
    by (rule rounds_positive)
  have openings0_nonempty:
    "trace_openings ! 0 \<noteq> []"
  proof -
    have "map opening_index (trace_openings ! 0) =
        powers_scaled (query_idxs ! 0)"
      by (rule indices[OF round0])
    moreover have "powers_scaled (query_idxs ! 0) \<noteq> []"
      using powers_pos unfolding powers_scaled_def by simp
    ultimately show ?thesis
      by auto
  qed
  then obtain opn where opn_in:
    "opn \<in> set (trace_openings ! 0)"
    by (cases "trace_openings ! 0") auto
  have table0:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! 0) final_state"
    using tables[OF round0] by simp
  have opn_root: "opening_root opn = fr"
    using table0 opn_in unfolding partial_authenticated_table_def by blast
  have opn_auth: "authenticated_opening_in final_state opn"
    using table0 opn_in unfolding partial_authenticated_table_def by blast
  from authenticated_opening_root_lookup[OF opn_auth]
  obtain input where lookup_final:
    "fmlookup (HashMap final_state) input = Some fr"
    using opn_root by auto
  have root_in: "fr \<in> set tr"
    using header tr_eq
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
  have ext: "s \<le> final_state"
    by (rule verify_monad_hash_extends[OF outcome])
  show ?thesis
  proof (cases "fmlookup (HashMap s) input")
    case None
    then have "hash_map_new_output_hit (set tr) s final_state"
      unfolding hash_map_new_output_hit_def
      using lookup_final root_in by blast
    then show ?thesis by simp
  next
    case (Some z)
    have lookup_final_z: "fmlookup (HashMap final_state) input = Some z"
      by (rule hash_extension_lookup[OF Some ext])
    then have "z = fr"
      using lookup_final by simp
    then have "fr \<in> hash_map_output_values s"
      using Some by (auto intro: hash_map_output_valuesI)
    then show ?thesis
      using root_in by blast
  qed
qed

definition soundness_bad_event_with_merkle
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "soundness_bad_event_with_merkle s out \<longleftrightarrow>
      fri_merkle_binding_bad s out \<or> soundness_bad_event s out"

lemma soundness_bad_event_imp_soundness_bad_event_with_merkle:
  assumes "soundness_bad_event s out"
  shows "soundness_bad_event_with_merkle s out"
  using assms unfolding soundness_bad_event_with_merkle_def by simp

lemma fri_merkle_binding_bad_imp_soundness_bad_event_with_merkle:
  assumes "fri_merkle_binding_bad s out"
  shows "soundness_bad_event_with_merkle s out"
  using assms unfolding soundness_bad_event_with_merkle_def by simp

lemma accepted_with_fri_tables_table_partition:
  assumes false_statement: "\<not> exists_valid_trace"
    and tables: "accepted_with_fri_tables s out"
  shows "soundness_bad_event s out"
proof -
  from accepted_with_fri_tables_obtain_bound_tables[OF tables]
  obtain trace_table composition_table as query_idxs where bound:
    "accepted_with_bound_tables s out trace_table composition_table as
      query_idxs"
    by blast
  have partition:
    "composition_bad s out \<or> trace_fri_bad s out \<or>
      composition_fri_bad s out \<or> query_bad s out"
    by (rule accepted_bound_table_partition[OF false_statement bound])
  then show ?thesis
    unfolding soundness_bad_event_def by blast
qed

lemma accepted_partition_soundness_bad_event_with_merkle:
  assumes false_statement: "\<not> exists_valid_trace"
    and acc: "accepted out"
  shows "soundness_bad_event_with_merkle s out"
proof -
  from accepted_partition_fri_merkle_binding[OF acc]
  consider
      (merkle_bad) "fri_merkle_binding_bad s out"
    | (with_tables) "accepted_with_fri_tables s out"
    by blast
  then show ?thesis
  proof cases
    case merkle_bad
    then show ?thesis
      by (rule fri_merkle_binding_bad_imp_soundness_bad_event_with_merkle)
  next
    case with_tables
    have "soundness_bad_event s out"
      by (rule accepted_with_fri_tables_table_partition
          [OF false_statement with_tables])
    then show ?thesis
      by (rule soundness_bad_event_imp_soundness_bad_event_with_merkle)
  qed
qed

definition trace_fri_challenge_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_challenge_set_hit s bad_sets out \<longleftrightarrow>
      (\<exists>trace_table composition_table as query_idxs trace_bs dg comp_bs.
        accepted_with_bound_tables s out trace_table composition_table as query_idxs \<and>
        accepted_fri_challenges s out trace_bs dg comp_bs \<and>
        \<not> trace_table_low_degree trace_table \<and>
        trace_bs \<in> bad_sets trace_table)"

definition composition_fri_challenge_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> 'f list set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_fri_challenge_set_hit s bad_sets out \<longleftrightarrow>
      (\<exists>trace_table composition_table as query_idxs trace_bs dg comp_bs.
        accepted_with_bound_tables s out trace_table composition_table as query_idxs \<and>
        accepted_fri_challenges s out trace_bs dg comp_bs \<and>
        trace_table_low_degree trace_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table \<and>
        comp_bs \<in> bad_sets dg composition_table)"

lemma trace_fri_challenge_set_hit_imp_list_set_hit:
  assumes hit: "trace_fri_challenge_set_hit s bad_sets out"
    and envelope: "\<And>trace_table. bad_sets trace_table \<subseteq> B"
  shows "trace_fri_challenge_list_set_hit s B out"
proof -
  from hit obtain trace_table composition_table as query_idxs trace_bs dg comp_bs
    where challenges:
      "accepted_fri_challenges s out trace_bs dg comp_bs"
    and trace_bad: "trace_bs \<in> bad_sets trace_table"
    unfolding trace_fri_challenge_set_hit_def by blast
  have "trace_bs \<in> B"
    using trace_bad envelope[of trace_table] by auto
  then show ?thesis
    unfolding trace_fri_challenge_list_set_hit_def
    using challenges by blast
qed

definition trace_fri_root_trace_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "trace_fri_root_trace_table_candidates s fr =
      {trace_table.
        \<exists>out composition_table as query_idxs trace_bs dg comp_bs
            f_fri_roots f_final header_as composition_fri_roots final rest.
          accepted_with_bound_tables s out trace_table composition_table
            as query_idxs \<and>
        accepted_fri_challenges s out trace_bs dg comp_bs \<and>
        verifier_header_transcript s fr f_fri_roots f_final header_as dg
          composition_fri_roots final rest}"

definition trace_fri_supported_root_trace_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "trace_fri_supported_root_trace_table_candidates s fr =
      {trace_table.
        \<exists>out composition_table as query_idxs trace_bs dg comp_bs
            f_fri_roots f_final header_as composition_fri_roots final rest.
          out \<in> set_dist (execute verify_monad s) \<and>
          accepted_with_bound_tables s out trace_table composition_table
            as query_idxs \<and>
          accepted_fri_challenges s out trace_bs dg comp_bs \<and>
          verifier_header_transcript s fr f_fri_roots f_final header_as dg
            composition_fri_roots final rest}"

definition trace_fri_supported_root_partial_trace_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "trace_fri_supported_root_partial_trace_table_candidates s fr =
      {trace_table.
        \<exists>out query_idxs trace_openings trace_bs dg comp_bs
            f_fri_roots f_final header_as composition_fri_roots final rest.
          out \<in> set_dist (execute verify_monad s) \<and>
          accepted_with_partial_trace_openings s out fr query_idxs
            trace_openings \<and>
          partial_trace_table_candidate trace_table trace_openings \<and>
          accepted_fri_challenges s out trace_bs dg comp_bs \<and>
          verifier_header_transcript s fr f_fri_roots f_final header_as dg
            composition_fri_roots final rest}"

definition trace_fri_supported_root_partial_trace_table_candidate_state
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "trace_fri_supported_root_partial_trace_table_candidate_state s fr
      trace_table final_state \<longleftrightarrow>
      (\<exists>result query_idxs trace_openings trace_bs dg comp_bs
          f_fri_roots f_final header_as composition_fri_roots final rest.
        Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
        accepted_with_partial_trace_openings s
          (Some (result, final_state)) fr query_idxs trace_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
          comp_bs \<and>
        verifier_header_transcript s fr f_fri_roots f_final header_as dg
          composition_fri_roots final rest)"

definition alpha_header_supported_partial_trace_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
      f_final =
      {trace_table.
        \<exists>out query_idxs trace_openings as dg composition_fri_roots final rest.
          out \<in> set_dist (execute verify_monad s) \<and>
          accepted_with_partial_trace_openings s out fr query_idxs
            trace_openings \<and>
          partial_trace_table_candidate trace_table trace_openings \<and>
          verifier_header_transcript s fr f_fri_roots f_final as dg
            composition_fri_roots final rest}"

lemma alpha_header_supported_partial_trace_table_candidatesE:
  assumes
    "trace_table \<in>
      alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
        f_final"
  obtains out query_idxs trace_openings as dg composition_fri_roots final rest
    where
      "out \<in> set_dist (execute verify_monad s)"
      "accepted_with_partial_trace_openings s out fr query_idxs
        trace_openings"
      "partial_trace_table_candidate trace_table trace_openings"
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  using assms
  unfolding alpha_header_supported_partial_trace_table_candidates_def
  by blast

definition alpha_header_supported_partial_union_bad_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "alpha_header_supported_partial_union_bad_sets s bad_sets fr
      f_fri_roots f_final =
      {as \<in> alpha_space.
        \<exists>trace_table \<in>
          alpha_header_supported_partial_trace_table_candidates s fr
            f_fri_roots f_final.
          as \<in> bad_sets trace_table}"

definition trace_fri_root_trace_table_candidate_state
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "trace_fri_root_trace_table_candidate_state s fr trace_table
      final_state \<longleftrightarrow>
      (\<exists>result composition_table as query_idxs trace_bs dg comp_bs
          f_fri_roots f_final header_as composition_fri_roots final rest.
        accepted_with_bound_tables s (Some (result, final_state))
          trace_table composition_table as query_idxs \<and>
        accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
          comp_bs \<and>
        verifier_header_transcript s fr f_fri_roots f_final header_as dg
          composition_fri_roots final rest \<and>
        merkle_root_binds_table fr trace_table final_state)"

definition trace_fri_supported_root_trace_table_candidate_state
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
      final_state \<longleftrightarrow>
      (\<exists>result composition_table as query_idxs trace_bs dg comp_bs
          f_fri_roots f_final header_as composition_fri_roots final rest.
        Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
        accepted_with_bound_tables s (Some (result, final_state))
          trace_table composition_table as query_idxs \<and>
        accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
          comp_bs \<and>
        verifier_header_transcript s fr f_fri_roots f_final header_as dg
          composition_fri_roots final rest \<and>
        merkle_root_binds_table fr trace_table final_state)"

lemma trace_fri_root_trace_table_candidates_iff_state:
  "trace_table \<in> trace_fri_root_trace_table_candidates s fr \<longleftrightarrow>
    (\<exists>final_state.
      trace_fri_root_trace_table_candidate_state s fr trace_table
        final_state)"
proof
  assume candidate:
    "trace_table \<in> trace_fri_root_trace_table_candidates s fr"
  then obtain out composition_table as query_idxs trace_bs dg comp_bs
      f_fri_roots f_final header_as composition_fri_roots final rest where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and challenges:
      "accepted_fri_challenges s out trace_bs dg comp_bs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final header_as dg
        composition_fri_roots final rest"
    unfolding trace_fri_root_trace_table_candidates_def by blast
  from bound obtain result final_state fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    out_eq: "out = Some (result, final_state)"
    and header':
      "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and bind:
      "merkle_root_binds_table fr' trace_table final_state"
    unfolding accepted_with_bound_tables_def by blast
  have fr_eq: "fr' = fr"
    using verifier_header_transcript_unique[OF header' header] by simp
  have bound_some:
    "accepted_with_bound_tables s (Some (result, final_state))
      trace_table composition_table as query_idxs"
    using bound out_eq by simp
  have challenges_some:
    "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
      comp_bs"
    using challenges out_eq by simp
  have bind_fr: "merkle_root_binds_table fr trace_table final_state"
    using bind fr_eq by simp
  have state:
    "trace_fri_root_trace_table_candidate_state s fr trace_table
      final_state"
    unfolding trace_fri_root_trace_table_candidate_state_def
    apply (rule exI[where x=result])
    apply (rule exI[where x=composition_table])
    apply (rule exI[where x=as])
    apply (rule exI[where x=query_idxs])
    apply (rule exI[where x=trace_bs])
    apply (rule exI[where x=dg])
    apply (rule exI[where x=comp_bs])
    apply (rule exI[where x=f_fri_roots])
    apply (rule exI[where x=f_final])
    apply (rule exI[where x=header_as])
    apply (rule exI[where x=composition_fri_roots])
    apply (rule exI[where x=final])
    apply (rule exI[where x=rest])
    apply (intro conjI)
       apply (rule bound_some)
      apply (rule challenges_some)
     apply (rule header)
    apply (rule bind_fr)
    done
  then show
    "\<exists>final_state.
      trace_fri_root_trace_table_candidate_state s fr trace_table
        final_state"
    by blast
next
  assume
    "\<exists>final_state.
      trace_fri_root_trace_table_candidate_state s fr trace_table
        final_state"
  then obtain final_state result composition_table as query_idxs trace_bs dg
      comp_bs f_fri_roots f_final header_as composition_fri_roots final rest
    where
    bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and challenges:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
        comp_bs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final header_as dg
        composition_fri_roots final rest"
    unfolding trace_fri_root_trace_table_candidate_state_def by blast
  show "trace_table \<in> trace_fri_root_trace_table_candidates s fr"
    unfolding trace_fri_root_trace_table_candidates_def
    using bound challenges header by blast
qed

lemma trace_fri_supported_root_trace_table_candidates_iff_state:
  "trace_table \<in> trace_fri_supported_root_trace_table_candidates s fr \<longleftrightarrow>
    (\<exists>final_state.
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state)"
proof
  assume candidate:
    "trace_table \<in> trace_fri_supported_root_trace_table_candidates s fr"
  then obtain out composition_table as query_idxs trace_bs dg comp_bs
      f_fri_roots f_final header_as composition_fri_roots final rest where
    outcome: "out \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and challenges:
      "accepted_fri_challenges s out trace_bs dg comp_bs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final header_as dg
        composition_fri_roots final rest"
    unfolding trace_fri_supported_root_trace_table_candidates_def by blast
  from bound obtain result final_state fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    out_eq: "out = Some (result, final_state)"
    and header':
      "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
        composition_fri_roots' final' rest'"
    and bind:
      "merkle_root_binds_table fr' trace_table final_state"
    unfolding accepted_with_bound_tables_def by blast
  have fr_eq: "fr' = fr"
    using verifier_header_transcript_unique[OF header' header] by simp
  have state:
    "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
      final_state"
    unfolding trace_fri_supported_root_trace_table_candidate_state_def
    apply (rule exI[where x=result])
    apply (rule exI[where x=composition_table])
    apply (rule exI[where x=as])
    apply (rule exI[where x=query_idxs])
    apply (rule exI[where x=trace_bs])
    apply (rule exI[where x=dg])
    apply (rule exI[where x=comp_bs])
    apply (rule exI[where x=f_fri_roots])
    apply (rule exI[where x=f_final])
    apply (rule exI[where x=header_as])
    apply (rule exI[where x=composition_fri_roots])
    apply (rule exI[where x=final])
    apply (rule exI[where x=rest])
    apply (intro conjI)
        apply (use outcome out_eq in simp)
       apply (use bound out_eq in simp)
      apply (use challenges out_eq in simp)
     apply (rule header)
    apply (use bind fr_eq in simp)
    done
  then show
    "\<exists>final_state.
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
    by blast
next
  assume
    "\<exists>final_state.
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
  then obtain final_state result composition_table as query_idxs trace_bs dg
      comp_bs f_fri_roots f_final header_as composition_fri_roots final rest
    where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and challenges:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
        comp_bs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final header_as dg
        composition_fri_roots final rest"
    unfolding trace_fri_supported_root_trace_table_candidate_state_def by blast
  show "trace_table \<in> trace_fri_supported_root_trace_table_candidates s fr"
    unfolding trace_fri_supported_root_trace_table_candidates_def
    using outcome bound challenges header by blast
qed

lemma trace_fri_supported_root_partial_trace_table_candidates_iff_state:
  "trace_table \<in>
      trace_fri_supported_root_partial_trace_table_candidates s fr \<longleftrightarrow>
    (\<exists>final_state.
      trace_fri_supported_root_partial_trace_table_candidate_state s fr
        trace_table final_state)"
proof
  assume candidate:
    "trace_table \<in>
      trace_fri_supported_root_partial_trace_table_candidates s fr"
  then obtain out query_idxs trace_openings trace_bs dg comp_bs
      f_fri_roots f_final header_as composition_fri_roots final rest where
    outcome: "out \<in> set_dist (execute verify_monad s)"
    and partial:
      "accepted_with_partial_trace_openings s out fr query_idxs
        trace_openings"
    and table:
      "partial_trace_table_candidate trace_table trace_openings"
    and challenges:
      "accepted_fri_challenges s out trace_bs dg comp_bs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final header_as dg
        composition_fri_roots final rest"
    unfolding trace_fri_supported_root_partial_trace_table_candidates_def
    by blast
  from partial obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_with_partial_trace_openings_def by blast
  have state:
    "trace_fri_supported_root_partial_trace_table_candidate_state s fr
      trace_table final_state"
  proof -
    have outcome_some:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
      using outcome out_eq by simp
    have partial_some:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
      using partial out_eq by simp
    have challenges_some:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
        comp_bs"
      using challenges out_eq by simp
    show ?thesis
      unfolding
        trace_fri_supported_root_partial_trace_table_candidate_state_def
      using outcome_some partial_some table challenges_some header by blast
  qed
  then show
    "\<exists>final_state.
      trace_fri_supported_root_partial_trace_table_candidate_state s fr
        trace_table final_state"
    by blast
next
  assume
    "\<exists>final_state.
      trace_fri_supported_root_partial_trace_table_candidate_state s fr
        trace_table final_state"
  then obtain final_state result query_idxs trace_openings trace_bs dg
      comp_bs f_fri_roots f_final header_as composition_fri_roots final rest
    where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    and table:
      "partial_trace_table_candidate trace_table trace_openings"
    and challenges:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
        comp_bs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final header_as dg
        composition_fri_roots final rest"
    unfolding
      trace_fri_supported_root_partial_trace_table_candidate_state_def
    by blast
  show
    "trace_table \<in>
      trace_fri_supported_root_partial_trace_table_candidates s fr"
    unfolding trace_fri_supported_root_partial_trace_table_candidates_def
    using outcome partial table challenges header by blast
qed

lemma trace_fri_supported_root_partial_trace_table_candidate_length:
  assumes
    "trace_fri_supported_root_partial_trace_table_candidate_state s fr
      trace_table final_state"
  shows "length trace_table = scale * clength"
  using assms
  unfolding trace_fri_supported_root_partial_trace_table_candidate_state_def
    partial_trace_table_candidate_def
  by blast

lemma alpha_header_supported_partial_union_bad_sets_subset_alpha_space:
  "alpha_header_supported_partial_union_bad_sets s bad_sets fr f_fri_roots
    f_final \<subseteq> alpha_space"
  unfolding alpha_header_supported_partial_union_bad_sets_def by auto

lemma trace_fri_supported_root_trace_table_candidate_state_imp_candidate_state:
  assumes
    "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
      final_state"
  shows
    "trace_fri_root_trace_table_candidate_state s fr trace_table final_state"
  using assms
  unfolding trace_fri_supported_root_trace_table_candidate_state_def
    trace_fri_root_trace_table_candidate_state_def
  by blast

lemma trace_fri_supported_root_trace_table_candidate_state_hash_extends:
  assumes
    "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
      final_state"
  shows "s \<le> final_state"
proof -
  from assms obtain result composition_table as query_idxs trace_bs dg comp_bs
      f_fri_roots f_final header_as composition_fri_roots final rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    unfolding trace_fri_supported_root_trace_table_candidate_state_def
    by blast
  show ?thesis
    by (rule verify_monad_hash_extends[OF outcome])
qed

lemma trace_fri_supported_root_trace_table_candidate_state_imp_partial_candidate:
  assumes state:
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
    and clean: "\<not> hash_map_output_collision final_state"
  shows
    "trace_table \<in>
      trace_fri_supported_root_partial_trace_table_candidates s fr"
proof -
  from state obtain result composition_table as query_idxs trace_bs dg comp_bs
      f_fri_roots f_final header_as composition_fri_roots final rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and challenges:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
        comp_bs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final header_as dg
        composition_fri_roots final rest"
    and bind:
      "merkle_root_binds_table fr trace_table final_state"
    unfolding trace_fri_supported_root_trace_table_candidate_state_def
    by blast
  from verify_monad_header_extraction[OF outcome]
  obtain fr' f_fl f_final' as' dg' fl final' query_state where
    header':
      "verifier_header_transcript s fr' (map snd f_fl) f_final' as' dg'
        (map snd fl) final' (PTranscript query_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr' f_fl f_final' as' fl final')
              rounds)
            query_state)"
    by (rule verify_monad_header_query_extraction[OF outcome])
  have fr_eq: "fr' = fr"
    using verifier_header_transcript_unique[OF header' header] by simp
  obtain query_idxs' trace_openings where
    len_query_idxs: "length query_idxs' = rounds"
    and len_openings: "length trace_openings = rounds"
    and indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs' ! i)"
    and tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table fr'
          (scale * clength) (trace_openings ! i) final_state"
  proof (rule ntimes_verifier_query_rounds_authenticated_trace_openings_no_raws
      [OF query_out])
    fix query_idxs' trace_openings
    assume len_query_idxs: "length query_idxs' = rounds"
      and len_openings: "length trace_openings = rounds"
      and indices:
        "\<And>i. i < rounds \<Longrightarrow>
          map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs' ! i)"
      and tables:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_authenticated_table fr'
            (scale * clength) (trace_openings ! i) final_state"
    show ?thesis
      by (rule that[OF len_query_idxs len_openings indices tables])
  qed
  have partial:
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr query_idxs' trace_openings"
  proof -
    have all_indices:
      "\<forall>i < rounds.
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs' ! i)"
      using indices by blast
    have all_tables:
      "\<forall>i < rounds.
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) final_state"
      using tables fr_eq by simp
    show ?thesis
      unfolding accepted_with_partial_trace_openings_def accepted_def
      by (intro conjI exI[of _ result] exI[of _ final_state])
        (use len_query_idxs len_openings all_indices all_tables in simp_all)
  qed
  have len_table: "length trace_table = scale * clength"
    using accepted_with_bound_tables_shapes(1)[OF bound] by simp
  have partial_candidate:
    "partial_trace_table_candidate trace_table trace_openings"
    by (rule accepted_bound_trace_table_partial_candidate_if_clean
        [OF bind len_table partial clean])
  show ?thesis
  proof -
    have witness:
      "\<exists>out query_idxs trace_openings trace_bs dg comp_bs
          f_fri_roots f_final header_as composition_fri_roots final rest.
        out \<in> set_dist (execute verify_monad s) \<and>
        accepted_with_partial_trace_openings s out fr query_idxs
          trace_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        accepted_fri_challenges s out trace_bs dg comp_bs \<and>
        verifier_header_transcript s fr f_fri_roots f_final header_as dg
          composition_fri_roots final rest"
      using outcome partial partial_candidate challenges header by blast
    show ?thesis
      using witness
      unfolding trace_fri_supported_root_partial_trace_table_candidates_def
      by simp
  qed
qed

lemma alpha_header_supported_trace_table_candidate_state_imp_partial_candidate:
  assumes state:
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
    and clean: "\<not> hash_map_output_collision final_state"
  shows
    "trace_table \<in>
      alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
        f_final"
proof -
  from state obtain result composition_table as query_idxs dg
      composition_fri_roots final rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and bind:
      "merkle_root_binds_table fr trace_table final_state"
    unfolding alpha_header_supported_trace_table_candidate_state_def
    by blast
  from verify_monad_header_extraction[OF outcome]
  obtain fr' f_fl f_final' as' dg' fl final' query_state where
    header':
      "verifier_header_transcript s fr' (map snd f_fl) f_final' as' dg'
        (map snd fl) final' (PTranscript query_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr' f_fl f_final' as' fl final')
              rounds)
            query_state)"
    by (rule verify_monad_header_query_extraction[OF outcome])
  have eqs:
    "fr' = fr \<and> map snd f_fl = f_fri_roots \<and>
     f_final' = f_final \<and> as' = as \<and> dg' = dg \<and>
     map snd fl = composition_fri_roots \<and> final' = final \<and>
     PTranscript query_state = rest"
    using verifier_header_transcript_unique[OF header' header] by simp
  obtain query_idxs' trace_openings where
    len_query_idxs: "length query_idxs' = rounds"
    and len_openings: "length trace_openings = rounds"
    and indices:
      "\<And>i. i < rounds \<Longrightarrow>
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs' ! i)"
    and tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table fr'
          (scale * clength) (trace_openings ! i) final_state"
  proof (rule ntimes_verifier_query_rounds_authenticated_trace_openings_no_raws
      [OF query_out])
    fix query_idxs' trace_openings
    assume len_query_idxs: "length query_idxs' = rounds"
      and len_openings: "length trace_openings = rounds"
      and indices:
        "\<And>i. i < rounds \<Longrightarrow>
          map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs' ! i)"
      and tables:
        "\<And>i. i < rounds \<Longrightarrow>
          partial_authenticated_table fr'
            (scale * clength) (trace_openings ! i) final_state"
    show ?thesis
      by (rule that[OF len_query_idxs len_openings indices tables])
  qed
  have partial:
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr query_idxs' trace_openings"
  proof -
    have all_indices:
      "\<forall>i < rounds.
        map opening_index (trace_openings ! i) =
          powers_scaled (query_idxs' ! i)"
      using indices by blast
    have all_tables:
      "\<forall>i < rounds.
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) final_state"
      using tables eqs by simp
    show ?thesis
      unfolding accepted_with_partial_trace_openings_def accepted_def
      by (intro conjI exI[of _ result] exI[of _ final_state])
        (use len_query_idxs len_openings all_indices all_tables in simp_all)
  qed
  have len_table: "length trace_table = scale * clength"
    using accepted_with_bound_tables_shapes(1)[OF bound] by simp
  have partial_candidate:
    "partial_trace_table_candidate trace_table trace_openings"
    by (rule accepted_bound_trace_table_partial_candidate_if_clean
        [OF bind len_table partial clean])
  show ?thesis
    unfolding alpha_header_supported_partial_trace_table_candidates_def
    by (intro CollectI exI[of _ "Some (result, final_state)"]
        exI[of _ query_idxs'] exI[of _ trace_openings]
        exI[of _ as] exI[of _ dg]
        exI[of _ composition_fri_roots] exI[of _ final]
        exI[of _ rest] conjI)
      (use outcome partial partial_candidate header in simp_all)
qed

lemma trace_fri_root_trace_table_candidate_states_common_extension_unique_if_clean:
  assumes clean: "\<not> hash_map_output_collision u"
    and candidate1:
      "trace_fri_root_trace_table_candidate_state s fr trace_table
        final_state"
    and candidate2:
      "trace_fri_root_trace_table_candidate_state s fr trace_table'
        final_state'"
    and ext1: "final_state \<le> u"
    and ext2: "final_state' \<le> u"
  shows "trace_table = trace_table'"
proof -
  from candidate1 obtain result composition_table as query_idxs trace_bs dg
      comp_bs f_fri_roots f_final header_as composition_fri_roots final rest
    where
    bound1:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and bind1: "merkle_root_binds_table fr trace_table final_state"
    unfolding trace_fri_root_trace_table_candidate_state_def by blast
  from candidate2 obtain result' composition_table' as' query_idxs' trace_bs'
      dg' comp_bs' f_fri_roots' f_final' header_as'
      composition_fri_roots' final' rest' where
    bound2:
      "accepted_with_bound_tables s (Some (result', final_state'))
        trace_table' composition_table' as' query_idxs'"
    and bind2: "merkle_root_binds_table fr trace_table' final_state'"
    unfolding trace_fri_root_trace_table_candidate_state_def by blast
  have same_len: "length trace_table = length trace_table'"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      accepted_with_bound_tables_shapes(1)[OF bound2]
    by simp
  have nonempty: "trace_table \<noteq> []"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      eval_domain_nontrivial by auto
  show ?thesis
    by (rule merkle_root_binds_same_length_tables_common_extension_unique_if_clean
        [OF clean bind1 bind2 ext1 ext2 same_len nonempty])
qed

lemma trace_fri_root_trace_table_candidate_states_compatible_unique_if_clean_merge:
  assumes compatible: "hash_maps_compatible final_state final_state'"
    and clean:
      "\<not> hash_map_output_collision
        (hash_state_merge final_state final_state')"
    and candidate1:
      "trace_fri_root_trace_table_candidate_state s fr trace_table
        final_state"
    and candidate2:
      "trace_fri_root_trace_table_candidate_state s fr trace_table'
        final_state'"
  shows "trace_table = trace_table'"
proof -
  from candidate1 obtain result composition_table as query_idxs trace_bs dg
      comp_bs f_fri_roots f_final header_as composition_fri_roots final rest
    where
    bound1:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and bind1: "merkle_root_binds_table fr trace_table final_state"
    unfolding trace_fri_root_trace_table_candidate_state_def by blast
  from candidate2 obtain result' composition_table' as' query_idxs' trace_bs'
      dg' comp_bs' f_fri_roots' f_final' header_as'
      composition_fri_roots' final' rest' where
    bound2:
      "accepted_with_bound_tables s (Some (result', final_state'))
        trace_table' composition_table' as' query_idxs'"
    and bind2: "merkle_root_binds_table fr trace_table' final_state'"
    unfolding trace_fri_root_trace_table_candidate_state_def by blast
  have same_len: "length trace_table = length trace_table'"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      accepted_with_bound_tables_shapes(1)[OF bound2]
    by simp
  have nonempty: "trace_table \<noteq> []"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      eval_domain_nontrivial by auto
  show ?thesis
    by (rule
        merkle_root_binds_same_length_tables_compatible_states_unique_if_clean_merge
        [OF compatible clean bind1 bind2 same_len nonempty])
qed

lemma trace_fri_root_trace_table_candidate_states_merkle_compatible_unique_if_clean_merge:
  assumes compatible:
      "merkle_hash_maps_compatible final_state final_state'"
    and clean:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    and candidate1:
      "trace_fri_root_trace_table_candidate_state s fr trace_table
        final_state"
    and candidate2:
      "trace_fri_root_trace_table_candidate_state s fr trace_table'
        final_state'"
  shows "trace_table = trace_table'"
proof -
  from candidate1 obtain result composition_table as query_idxs trace_bs dg
      comp_bs f_fri_roots f_final header_as composition_fri_roots final rest
    where
    bound1:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and bind1: "merkle_root_binds_table fr trace_table final_state"
    unfolding trace_fri_root_trace_table_candidate_state_def by blast
  from candidate2 obtain result' composition_table' as' query_idxs' trace_bs'
      dg' comp_bs' f_fri_roots' f_final' header_as'
      composition_fri_roots' final' rest' where
    bound2:
      "accepted_with_bound_tables s (Some (result', final_state'))
        trace_table' composition_table' as' query_idxs'"
    and bind2: "merkle_root_binds_table fr trace_table' final_state'"
    unfolding trace_fri_root_trace_table_candidate_state_def by blast
  have same_len: "length trace_table = length trace_table'"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      accepted_with_bound_tables_shapes(1)[OF bound2]
    by simp
  have nonempty: "trace_table \<noteq> []"
    using accepted_with_bound_tables_shapes(1)[OF bound1]
      eval_domain_nontrivial by auto
  show ?thesis
    by (rule
        merkle_root_binds_same_length_tables_merkle_compatible_unique_if_clean_merge
        [OF compatible clean bind1 bind2 same_len nonempty])
qed

lemma trace_fri_root_trace_table_candidates_subset_singleton_if_common_clean_extension:
  assumes clean: "\<not> hash_map_output_collision u"
    and common_ext:
      "\<And>trace_table final_state.
        trace_fri_root_trace_table_candidate_state s fr trace_table
          final_state \<Longrightarrow>
        final_state \<le> u"
  shows
    "\<exists>trace_table.
      trace_fri_root_trace_table_candidates s fr \<subseteq> {trace_table}"
proof (cases "trace_fri_root_trace_table_candidates s fr = {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"]) simp
next
  case False
  then obtain trace_table0 where table0:
    "trace_table0 \<in> trace_fri_root_trace_table_candidates s fr"
    by blast
  then obtain final_state0 where state0:
    "trace_fri_root_trace_table_candidate_state s fr trace_table0
      final_state0"
    using trace_fri_root_trace_table_candidates_iff_state by blast
  have ext0: "final_state0 \<le> u"
    by (rule common_ext[OF state0])
  have subset:
    "trace_fri_root_trace_table_candidates s fr \<subseteq> {trace_table0}"
  proof
    fix trace_table
    assume table:
      "trace_table \<in> trace_fri_root_trace_table_candidates s fr"
    then obtain final_state where state:
      "trace_fri_root_trace_table_candidate_state s fr trace_table
        final_state"
      using trace_fri_root_trace_table_candidates_iff_state by blast
    have ext: "final_state \<le> u"
      by (rule common_ext[OF state])
    have "trace_table = trace_table0"
      by (rule
          trace_fri_root_trace_table_candidate_states_common_extension_unique_if_clean
          [OF clean state state0 ext ext0])
    then show "trace_table \<in> {trace_table0}"
      by simp
  qed
  then show ?thesis
    by blast
qed

lemma trace_fri_root_trace_table_candidates_subset_singleton_if_pairwise_clean_merge:
  assumes pairwise:
      "\<And>trace_table final_state trace_table' final_state'.
        trace_fri_root_trace_table_candidate_state s fr trace_table
          final_state \<Longrightarrow>
        trace_fri_root_trace_table_candidate_state s fr trace_table'
          final_state' \<Longrightarrow>
        hash_maps_compatible final_state final_state' \<and>
        \<not> hash_map_output_collision
          (hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table.
      trace_fri_root_trace_table_candidates s fr \<subseteq> {trace_table}"
proof (cases "trace_fri_root_trace_table_candidates s fr = {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"]) simp
next
  case False
  then obtain trace_table0 where table0:
    "trace_table0 \<in> trace_fri_root_trace_table_candidates s fr"
    by blast
  then obtain final_state0 where state0:
    "trace_fri_root_trace_table_candidate_state s fr trace_table0
      final_state0"
    using trace_fri_root_trace_table_candidates_iff_state by blast
  have subset:
    "trace_fri_root_trace_table_candidates s fr \<subseteq> {trace_table0}"
  proof
    fix trace_table
    assume table:
      "trace_table \<in> trace_fri_root_trace_table_candidates s fr"
    then obtain final_state where state:
      "trace_fri_root_trace_table_candidate_state s fr trace_table
        final_state"
      using trace_fri_root_trace_table_candidates_iff_state by blast
    have compatible:
      "hash_maps_compatible final_state final_state0"
      using pairwise[OF state state0] by simp
    have clean:
      "\<not> hash_map_output_collision
        (hash_state_merge final_state final_state0)"
      using pairwise[OF state state0] by simp
    have "trace_table = trace_table0"
      by (rule
          trace_fri_root_trace_table_candidate_states_compatible_unique_if_clean_merge
          [OF compatible clean state state0])
    then show "trace_table \<in> {trace_table0}"
      by simp
  qed
  then show ?thesis
    by blast
qed

lemma trace_fri_supported_root_trace_table_candidates_subset_singleton_if_pairwise_clean_merge:
  assumes pairwise:
      "\<And>trace_table final_state trace_table' final_state'.
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table
          final_state \<Longrightarrow>
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
          final_state' \<Longrightarrow>
        hash_maps_compatible final_state final_state' \<and>
        \<not> hash_map_output_collision
          (hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table.
      trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
        {trace_table}"
proof (cases "trace_fri_supported_root_trace_table_candidates s fr = {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"]) simp
next
  case False
  then obtain trace_table0 where table0:
    "trace_table0 \<in> trace_fri_supported_root_trace_table_candidates s fr"
    by blast
  then obtain final_state0 where state0:
    "trace_fri_supported_root_trace_table_candidate_state s fr trace_table0
      final_state0"
    using trace_fri_supported_root_trace_table_candidates_iff_state by blast
  have state0_plain:
    "trace_fri_root_trace_table_candidate_state s fr trace_table0
      final_state0"
    by (rule
        trace_fri_supported_root_trace_table_candidate_state_imp_candidate_state
        [OF state0])
  have subset:
    "trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
      {trace_table0}"
  proof
    fix trace_table
    assume table:
      "trace_table \<in> trace_fri_supported_root_trace_table_candidates s fr"
    then obtain final_state where state:
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
      using trace_fri_supported_root_trace_table_candidates_iff_state by blast
    have state_plain:
      "trace_fri_root_trace_table_candidate_state s fr trace_table
        final_state"
      by (rule
          trace_fri_supported_root_trace_table_candidate_state_imp_candidate_state
          [OF state])
    have compatible:
      "hash_maps_compatible final_state final_state0"
      using pairwise[OF state state0] by simp
    have clean:
      "\<not> hash_map_output_collision
        (hash_state_merge final_state final_state0)"
      using pairwise[OF state state0] by simp
    have "trace_table = trace_table0"
      by (rule
          trace_fri_root_trace_table_candidate_states_compatible_unique_if_clean_merge
          [OF compatible clean state_plain state0_plain])
    then show "trace_table \<in> {trace_table0}"
      by simp
  qed
  then show ?thesis
    by blast
qed

lemma trace_fri_supported_root_trace_table_candidates_subset_singleton_if_pairwise_no_value_conflict_clean_merge:
  assumes pairwise:
      "\<And>trace_table final_state trace_table' final_state'.
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table
          final_state \<Longrightarrow>
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
          final_state' \<Longrightarrow>
        \<not> hash_map_value_conflict final_state final_state' \<and>
        \<not> hash_map_output_collision
          (hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table.
      trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
        {trace_table}"
proof (rule
    trace_fri_supported_root_trace_table_candidates_subset_singleton_if_pairwise_clean_merge)
  fix trace_table final_state trace_table' final_state'
  assume candidate:
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
    and candidate':
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
        final_state'"
  have no_conflict:
    "\<not> hash_map_value_conflict final_state final_state'"
    using pairwise[OF candidate candidate'] by simp
  have compatible:
    "hash_maps_compatible final_state final_state'"
    using no_conflict
    unfolding hash_maps_compatible_iff_no_value_conflict .
  have clean:
    "\<not> hash_map_output_collision
      (hash_state_merge final_state final_state')"
    using pairwise[OF candidate candidate'] by simp
  show "hash_maps_compatible final_state final_state' \<and>
      \<not> hash_map_output_collision
        (hash_state_merge final_state final_state')"
    using compatible clean by simp
qed

lemma trace_fri_supported_root_trace_table_candidates_subset_singleton_if_pairwise_merkle_clean_merge:
  assumes pairwise:
      "\<And>trace_table final_state trace_table' final_state'.
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table
          final_state \<Longrightarrow>
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
          final_state' \<Longrightarrow>
        merkle_hash_maps_compatible final_state final_state' \<and>
        \<not> hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table.
      trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
        {trace_table}"
proof (cases "trace_fri_supported_root_trace_table_candidates s fr = {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"]) simp
next
  case False
  then obtain trace_table0 where table0:
    "trace_table0 \<in> trace_fri_supported_root_trace_table_candidates s fr"
    by blast
  then obtain final_state0 where state0:
    "trace_fri_supported_root_trace_table_candidate_state s fr trace_table0
      final_state0"
    using trace_fri_supported_root_trace_table_candidates_iff_state by blast
  have state0_plain:
    "trace_fri_root_trace_table_candidate_state s fr trace_table0
      final_state0"
    by (rule
        trace_fri_supported_root_trace_table_candidate_state_imp_candidate_state
        [OF state0])
  have subset:
    "trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
      {trace_table0}"
  proof
    fix trace_table
    assume table:
      "trace_table \<in> trace_fri_supported_root_trace_table_candidates s fr"
    then obtain final_state where state:
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
      using trace_fri_supported_root_trace_table_candidates_iff_state by blast
    have state_plain:
      "trace_fri_root_trace_table_candidate_state s fr trace_table
        final_state"
      by (rule
          trace_fri_supported_root_trace_table_candidate_state_imp_candidate_state
          [OF state])
    have compatible:
      "merkle_hash_maps_compatible final_state final_state0"
      using pairwise[OF state state0] by simp
    have clean:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state0)"
      using pairwise[OF state state0] by simp
    have "trace_table = trace_table0"
      by (rule
          trace_fri_root_trace_table_candidate_states_merkle_compatible_unique_if_clean_merge
          [OF compatible clean state_plain state0_plain])
    then show "trace_table \<in> {trace_table0}"
      by simp
  qed
  then show ?thesis
    by blast
qed

lemma trace_fri_supported_root_trace_table_candidates_subset_singleton_if_pairwise_no_merkle_value_conflict_clean_merge:
  assumes pairwise:
      "\<And>trace_table final_state trace_table' final_state'.
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table
          final_state \<Longrightarrow>
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
          final_state' \<Longrightarrow>
        \<not> merkle_hash_value_conflict final_state final_state' \<and>
        \<not> hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table.
      trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
        {trace_table}"
proof (rule
    trace_fri_supported_root_trace_table_candidates_subset_singleton_if_pairwise_merkle_clean_merge)
  fix trace_table final_state trace_table' final_state'
  assume candidate:
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
    and candidate':
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
        final_state'"
  have no_conflict:
    "\<not> merkle_hash_value_conflict final_state final_state'"
    using pairwise[OF candidate candidate'] by simp
  have compatible:
    "merkle_hash_maps_compatible final_state final_state'"
    using no_conflict
    unfolding merkle_hash_maps_compatible_iff_no_value_conflict .
  have clean:
    "\<not> hash_map_output_collision
      (merkle_hash_state_merge final_state final_state')"
    using pairwise[OF candidate candidate'] by simp
  show "merkle_hash_maps_compatible final_state final_state' \<and>
      \<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    using compatible clean by simp
qed

lemma trace_fri_supported_root_trace_table_candidates_subset_singleton_if_common_clean_merkle_extension:
  assumes clean: "\<not> hash_map_output_collision u"
    and common_ext:
      "\<And>trace_table final_state.
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table
          final_state \<Longrightarrow>
        merkle_hash_extends final_state u"
  shows
    "\<exists>trace_table.
      trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
        {trace_table}"
proof (rule
    trace_fri_supported_root_trace_table_candidates_subset_singleton_if_pairwise_no_merkle_value_conflict_clean_merge)
  fix trace_table final_state trace_table' final_state'
  assume candidate:
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
    and candidate':
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
        final_state'"
  have ext: "merkle_hash_extends final_state u"
    by (rule common_ext[OF candidate])
  have ext': "merkle_hash_extends final_state' u"
    by (rule common_ext[OF candidate'])
  show "\<not> merkle_hash_value_conflict final_state final_state' \<and>
      \<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    by (rule common_clean_merkle_extension_imp_pairwise_merkle_clean
        [OF ext ext' clean])
qed

lemma trace_fri_supported_root_trace_table_candidate_states_distinct_imp_merkle_conflict_or_merge_collision:
  assumes candidate:
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
    and candidate':
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
        final_state'"
    and distinct_tables: "trace_table \<noteq> trace_table'"
  shows
    "merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
proof (rule ccontr)
  assume no_bad:
    "\<not> (merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state'))"
  have compatible:
    "merkle_hash_maps_compatible final_state final_state'"
    using no_bad unfolding merkle_hash_maps_compatible_iff_no_value_conflict
    by simp
  have clean:
    "\<not> hash_map_output_collision
      (merkle_hash_state_merge final_state final_state')"
    using no_bad by simp
  have candidate_plain:
    "trace_fri_root_trace_table_candidate_state s fr trace_table
      final_state"
    by (rule
        trace_fri_supported_root_trace_table_candidate_state_imp_candidate_state
        [OF candidate])
  have candidate_plain':
    "trace_fri_root_trace_table_candidate_state s fr trace_table'
      final_state'"
    by (rule
        trace_fri_supported_root_trace_table_candidate_state_imp_candidate_state
        [OF candidate'])
  have "trace_table = trace_table'"
    by (rule
        trace_fri_root_trace_table_candidate_states_merkle_compatible_unique_if_clean_merge
        [OF compatible clean candidate_plain candidate_plain'])
  then show False
    using distinct_tables by contradiction
qed

lemma trace_fri_supported_root_trace_table_candidates_not_singleton_imp_pairwise_merkle_bad:
  assumes not_unique:
      "\<not> (\<exists>trace_table.
        trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
          {trace_table})"
  shows
    "\<exists>trace_table final_state trace_table' final_state'.
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state \<and>
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
        final_state' \<and>
      trace_table \<noteq> trace_table' \<and>
      (merkle_hash_value_conflict final_state final_state' \<or>
        hash_map_output_collision
          (merkle_hash_state_merge final_state final_state'))"
proof -
  let ?C = "trace_fri_supported_root_trace_table_candidates s fr"
  have nonempty: "?C \<noteq> {}"
    using not_unique by auto
  then obtain trace_table where table: "trace_table \<in> ?C"
    by blast
  have "\<not> ?C \<subseteq> {trace_table}"
    using not_unique by blast
  then obtain trace_table' where table':
      "trace_table' \<in> ?C"
    and distinct_tables: "trace_table \<noteq> trace_table'"
    by auto
  from table obtain final_state where candidate:
    "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
      final_state"
    using trace_fri_supported_root_trace_table_candidates_iff_state by blast
  from table' obtain final_state' where candidate':
    "trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
      final_state'"
    using trace_fri_supported_root_trace_table_candidates_iff_state by blast
  have bad:
    "merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    by (rule
        trace_fri_supported_root_trace_table_candidate_states_distinct_imp_merkle_conflict_or_merge_collision
        [OF candidate candidate' distinct_tables])
  show ?thesis
    using candidate candidate' distinct_tables bad by blast
qed

definition trace_fri_supported_root_pairwise_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "trace_fri_supported_root_pairwise_merkle_bad s fr \<longleftrightarrow>
      (\<exists>trace_table final_state trace_table' final_state'.
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table
          final_state \<and>
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
          final_state' \<and>
        trace_table \<noteq> trace_table' \<and>
        (merkle_hash_value_conflict final_state final_state' \<or>
          hash_map_output_collision
            (merkle_hash_state_merge final_state final_state')))"

definition trace_fri_supported_pairwise_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "trace_fri_supported_pairwise_merkle_bad s \<longleftrightarrow>
      (\<exists>fr. trace_fri_supported_root_pairwise_merkle_bad s fr)"

lemma trace_fri_supported_root_pairwise_merkle_bad_extends_initial:
  assumes bad: "trace_fri_supported_root_pairwise_merkle_bad s fr"
  obtains trace_table final_state trace_table' final_state'
  where
    "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
      final_state"
    "trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
      final_state'"
    "trace_table \<noteq> trace_table'"
    "merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    "s \<le> final_state"
    "s \<le> final_state'"
proof -
  from bad obtain trace_table final_state trace_table' final_state' where
    candidate:
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
    and candidate':
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
        final_state'"
    and distinct: "trace_table \<noteq> trace_table'"
    and pair_bad:
      "merkle_hash_value_conflict final_state final_state' \<or>
        hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
    unfolding trace_fri_supported_root_pairwise_merkle_bad_def by blast
  have ext: "s \<le> final_state"
    by (rule trace_fri_supported_root_trace_table_candidate_state_hash_extends
        [OF candidate])
  have ext': "s \<le> final_state'"
    by (rule trace_fri_supported_root_trace_table_candidate_state_hash_extends
        [OF candidate'])
  show ?thesis
    by (rule that[OF candidate candidate' distinct pair_bad ext ext'])
qed

definition trace_fri_supported_root_pairwise_coupling_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "trace_fri_supported_root_pairwise_coupling_bad s fr \<longleftrightarrow>
      (\<exists>trace_table final_state trace_table' final_state'.
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table
          final_state \<and>
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
          final_state' \<and>
        trace_table \<noteq> trace_table' \<and>
        merkle_hash_pairwise_coupling_bad final_state final_state')"

definition trace_fri_supported_pairwise_coupling_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "trace_fri_supported_pairwise_coupling_bad s \<longleftrightarrow>
      (\<exists>fr. trace_fri_supported_root_pairwise_coupling_bad s fr)"

lemma trace_fri_supported_root_pairwise_merkle_bad_imp_local_collision_or_coupling_bad:
  assumes bad: "trace_fri_supported_root_pairwise_merkle_bad s fr"
  shows
    "(\<exists>trace_table final_state trace_table' final_state'.
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state \<and>
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
        final_state' \<and>
      trace_table \<noteq> trace_table' \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')) \<or>
     trace_fri_supported_root_pairwise_coupling_bad s fr"
proof -
  from bad obtain trace_table final_state trace_table' final_state'
    where candidate:
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
    and candidate':
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
        final_state'"
    and distinct: "trace_table \<noteq> trace_table'"
    and pair_bad:
      "merkle_hash_value_conflict final_state final_state' \<or>
        hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
    unfolding trace_fri_supported_root_pairwise_merkle_bad_def by blast
  have decomp:
    "hash_map_output_collision final_state \<or>
     hash_map_output_collision final_state' \<or>
     merkle_hash_pairwise_coupling_bad final_state final_state'"
    by (rule merkle_hash_pairwise_bad_imp_local_collision_or_coupling_bad
        [OF pair_bad])
  show ?thesis
    using candidate candidate' distinct decomp
    unfolding trace_fri_supported_root_pairwise_coupling_bad_def by blast
qed

lemma trace_fri_supported_pairwise_merkle_bad_imp_local_collision_or_coupling_bad:
  assumes bad: "trace_fri_supported_pairwise_merkle_bad s"
  shows
    "(\<exists>fr trace_table final_state trace_table' final_state'.
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state \<and>
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
        final_state' \<and>
      trace_table \<noteq> trace_table' \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')) \<or>
     trace_fri_supported_pairwise_coupling_bad s"
proof -
  from bad obtain fr where root_bad:
    "trace_fri_supported_root_pairwise_merkle_bad s fr"
    unfolding trace_fri_supported_pairwise_merkle_bad_def by blast
  from
    trace_fri_supported_root_pairwise_merkle_bad_imp_local_collision_or_coupling_bad
      [OF root_bad]
  show ?thesis
    unfolding trace_fri_supported_pairwise_coupling_bad_def by blast
qed

lemma trace_fri_supported_pairwise_merkle_bad_imp_supported_hash_collision_possible_or_coupling_bad:
  assumes bad: "trace_fri_supported_pairwise_merkle_bad s"
  shows
    "supported_hash_output_collision_possible s \<or>
     trace_fri_supported_pairwise_coupling_bad s"
proof -
  have decomp:
    "(\<exists>fr trace_table final_state trace_table' final_state'.
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state \<and>
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
        final_state' \<and>
      trace_table \<noteq> trace_table' \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')) \<or>
     trace_fri_supported_pairwise_coupling_bad s"
    by (rule
        trace_fri_supported_pairwise_merkle_bad_imp_local_collision_or_coupling_bad
        [OF bad])
  then show ?thesis
  proof
    assume local:
      "\<exists>fr trace_table final_state trace_table' final_state'.
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state \<and>
      trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
        final_state' \<and>
      trace_table \<noteq> trace_table' \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')"
    then obtain fr trace_table final_state trace_table' final_state' where
      candidate:
        "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
          final_state"
      and candidate':
        "trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
          final_state'"
      and collision:
        "hash_map_output_collision final_state \<or>
         hash_map_output_collision final_state'"
      by blast
    from collision show ?thesis
    proof
      assume collision_final: "hash_map_output_collision final_state"
      from candidate obtain result composition_table as query_idxs trace_bs dg
          comp_bs f_fri_roots f_final header_as composition_fri_roots final
          rest where
        outcome:
          "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
        and bound:
          "accepted_with_bound_tables s (Some (result, final_state))
            trace_table composition_table as query_idxs"
        unfolding trace_fri_supported_root_trace_table_candidate_state_def
        by blast
      have "supported_hash_output_collision_possible s"
        by (rule
            accepted_with_bound_tables_hash_collision_imp_supported_hash_output_collision_possible
            [OF outcome bound collision_final])
      then show ?thesis by simp
    next
      assume collision_final': "hash_map_output_collision final_state'"
      from candidate' obtain result' composition_table' as' query_idxs'
          trace_bs' dg' comp_bs' f_fri_roots' f_final' header_as'
          composition_fri_roots' final' rest' where
        outcome':
          "Some (result', final_state') \<in> set_dist (execute verify_monad s)"
        and bound':
          "accepted_with_bound_tables s (Some (result', final_state'))
            trace_table' composition_table' as' query_idxs'"
        unfolding trace_fri_supported_root_trace_table_candidate_state_def
        by blast
      have "supported_hash_output_collision_possible s"
        by (rule
            accepted_with_bound_tables_hash_collision_imp_supported_hash_output_collision_possible
            [OF outcome' bound' collision_final'])
      then show ?thesis by simp
    qed
  next
    assume "trace_fri_supported_pairwise_coupling_bad s"
    then show ?thesis by simp
  qed
qed

lemma trace_fri_supported_root_candidate_unique_if_no_pairwise_merkle_bad:
  assumes no_bad: "\<not> trace_fri_supported_root_pairwise_merkle_bad s fr"
  shows
    "\<exists>trace_table.
      trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
        {trace_table}"
proof (rule ccontr)
  assume not_unique:
    "\<not> (\<exists>trace_table.
      trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
        {trace_table})"
  have "trace_fri_supported_root_pairwise_merkle_bad s fr"
    using
      trace_fri_supported_root_trace_table_candidates_not_singleton_imp_pairwise_merkle_bad
        [OF not_unique]
    unfolding trace_fri_supported_root_pairwise_merkle_bad_def
    by blast
  then show False
    using no_bad by contradiction
qed

lemma trace_fri_supported_root_candidate_unique_if_no_global_pairwise_merkle_bad:
  assumes no_bad: "\<not> trace_fri_supported_pairwise_merkle_bad s"
  shows
    "\<exists>trace_table.
      trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
        {trace_table}"
proof (rule trace_fri_supported_root_candidate_unique_if_no_pairwise_merkle_bad)
  show "\<not> trace_fri_supported_root_pairwise_merkle_bad s fr"
    using no_bad unfolding trace_fri_supported_pairwise_merkle_bad_def by blast
qed

definition trace_fri_root_union_bad_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "trace_fri_root_union_bad_sets s bad_sets fr =
      {trace_bs \<in> fri_challenge_space (ceil_log clength).
        \<exists>trace_table \<in> trace_fri_root_trace_table_candidates s fr.
          trace_bs \<in> bad_sets trace_table}"

definition trace_fri_supported_root_union_bad_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "trace_fri_supported_root_union_bad_sets s bad_sets fr =
      {trace_bs \<in> fri_challenge_space (ceil_log clength).
        \<exists>trace_table \<in>
          trace_fri_supported_root_trace_table_candidates s fr.
          trace_bs \<in> bad_sets trace_table}"

definition trace_fri_supported_root_partial_union_bad_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow> 'f \<Rightarrow> 'f list set"
  where
    "trace_fri_supported_root_partial_union_bad_sets s bad_sets fr =
      {trace_bs \<in> fri_challenge_space (ceil_log clength).
        \<exists>trace_table \<in>
          trace_fri_supported_root_partial_trace_table_candidates s fr.
          trace_bs \<in> bad_sets trace_table}"

lemma trace_fri_root_union_bad_sets_subset:
  "trace_fri_root_union_bad_sets s bad_sets fr \<subseteq>
    fri_challenge_space (ceil_log clength)"
  unfolding trace_fri_root_union_bad_sets_def by auto

lemma trace_fri_supported_root_union_bad_sets_subset:
  "trace_fri_supported_root_union_bad_sets s bad_sets fr \<subseteq>
    fri_challenge_space (ceil_log clength)"
  unfolding trace_fri_supported_root_union_bad_sets_def by auto

lemma trace_fri_supported_root_partial_union_bad_sets_subset:
  "trace_fri_supported_root_partial_union_bad_sets s bad_sets fr \<subseteq>
    fri_challenge_space (ceil_log clength)"
  unfolding trace_fri_supported_root_partial_union_bad_sets_def by auto

lemma trace_fri_challenge_set_hit_imp_root_union_list_set_hit:
  assumes hit: "trace_fri_challenge_set_hit s bad_sets out"
  shows
    "trace_fri_root_list_set_hit s
      (trace_fri_root_union_bad_sets s bad_sets) out"
proof -
  from hit obtain trace_table composition_table as query_idxs trace_bs dg comp_bs
    where bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and challenges: "accepted_fri_challenges s out trace_bs dg comp_bs"
    and trace_bs_bad: "trace_bs \<in> bad_sets trace_table"
    unfolding trace_fri_challenge_set_hit_def by blast
  have header_ex:
    "\<exists>fr f_fri_roots f_final header_as composition_fri_roots final rest.
      verifier_header_transcript s fr f_fri_roots f_final header_as dg
        composition_fri_roots final rest"
  proof -
    from challenges[unfolded accepted_fri_challenges_def] show ?thesis
    proof (elim exE conjE)
      fix result0 final_state0 fr0 f_fl0 f_final0 as0 fl0 final0
        query_state0
      assume out0: "out = Some (result0, final_state0)"
        and header0:
          "verifier_header_transcript s fr0 (map snd f_fl0) f_final0 as0 dg
            (map snd fl0) final0 (PTranscript query_state0)"
      show ?thesis
        apply (rule exI[where x=fr0])
        apply (rule exI[where x="map snd f_fl0"])
        apply (rule exI[where x=f_final0])
        apply (rule exI[where x=as0])
        apply (rule exI[where x="map snd fl0"])
        apply (rule exI[where x=final0])
        apply (rule exI[where x="PTranscript query_state0"])
        apply (rule header0)
        done
    qed
  qed
  then obtain fr f_fri_roots f_final header_as composition_fri_roots final
      rest where
    header:
      "verifier_header_transcript s fr f_fri_roots f_final header_as dg
        composition_fri_roots final rest"
    by blast
  have candidate:
    "trace_table \<in> trace_fri_root_trace_table_candidates s fr"
    unfolding trace_fri_root_trace_table_candidates_def
    using bound challenges header by blast
  have trace_bs_space:
    "trace_bs \<in> fri_challenge_space (ceil_log clength)"
    by (rule accepted_fri_challenges_trace_space[OF challenges])
  have trace_bs_union:
    "trace_bs \<in> trace_fri_root_union_bad_sets s bad_sets fr"
    unfolding trace_fri_root_union_bad_sets_def
    using trace_bs_space candidate trace_bs_bad by blast
  show ?thesis
    unfolding trace_fri_root_list_set_hit_def
    using challenges header trace_bs_union by blast
qed

lemma trace_fri_challenge_set_hit_imp_supported_root_union_list_set_hit:
  assumes outcome: "out \<in> set_dist (execute verify_monad s)"
    and hit: "trace_fri_challenge_set_hit s bad_sets out"
  shows
    "trace_fri_root_list_set_hit s
      (trace_fri_supported_root_union_bad_sets s bad_sets) out"
proof -
  from hit obtain trace_table composition_table as query_idxs trace_bs dg comp_bs
    where bound:
        "accepted_with_bound_tables s out trace_table composition_table as
          query_idxs"
      and challenges: "accepted_fri_challenges s out trace_bs dg comp_bs"
      and not_low: "\<not> trace_table_low_degree trace_table"
      and trace_bs_bad: "trace_bs \<in> bad_sets trace_table"
    unfolding trace_fri_challenge_set_hit_def by blast
  have header_ex:
    "\<exists>fr f_fri_roots f_final header_as composition_fri_roots final rest.
      verifier_header_transcript s fr f_fri_roots f_final header_as dg
        composition_fri_roots final rest"
  proof -
    from challenges[unfolded accepted_fri_challenges_def] show ?thesis
    proof (elim exE conjE)
      fix result0 final_state0 fr0 f_fl0 f_final0 as0 fl0 final0
        query_state0
      assume
        header0:
          "verifier_header_transcript s fr0 (map snd f_fl0) f_final0 as0 dg
            (map snd fl0) final0 (PTranscript query_state0)"
      show ?thesis
        apply (rule exI[where x=fr0])
        apply (rule exI[where x="map snd f_fl0"])
        apply (rule exI[where x=f_final0])
        apply (rule exI[where x=as0])
        apply (rule exI[where x="map snd fl0"])
        apply (rule exI[where x=final0])
        apply (rule exI[where x="PTranscript query_state0"])
        apply (rule header0)
        done
    qed
  qed
  then obtain fr f_fri_roots f_final header_as composition_fri_roots final
      rest where
    header:
      "verifier_header_transcript s fr f_fri_roots f_final header_as dg
        composition_fri_roots final rest"
    by blast
  have candidate:
    "trace_table \<in> trace_fri_supported_root_trace_table_candidates s fr"
    unfolding trace_fri_supported_root_trace_table_candidates_def
    using outcome bound challenges header by blast
  have trace_bs_space:
    "trace_bs \<in> fri_challenge_space (ceil_log clength)"
    by (rule accepted_fri_challenges_trace_space[OF challenges])
  have trace_bs_union:
    "trace_bs \<in> trace_fri_supported_root_union_bad_sets s bad_sets fr"
    unfolding trace_fri_supported_root_union_bad_sets_def
    using trace_bs_space candidate trace_bs_bad by blast
  show ?thesis
    unfolding trace_fri_root_list_set_hit_def
    using challenges header trace_bs_union by blast
qed

lemma trace_fri_challenge_set_hit_imp_partial_union_or_collision:
  assumes outcome: "out \<in> set_dist (execute verify_monad s)"
    and hit: "trace_fri_challenge_set_hit s bad_sets out"
  shows
    "trace_fri_root_list_set_hit s
      (trace_fri_supported_root_partial_union_bad_sets s bad_sets) out \<or>
     hash_map_output_collision_bad s out"
proof -
  from hit obtain trace_table composition_table as query_idxs trace_bs dg comp_bs
    where bound:
        "accepted_with_bound_tables s out trace_table composition_table as
          query_idxs"
      and challenges: "accepted_fri_challenges s out trace_bs dg comp_bs"
      and not_low: "\<not> trace_table_low_degree trace_table"
      and trace_bs_bad: "trace_bs \<in> bad_sets trace_table"
    unfolding trace_fri_challenge_set_hit_def by blast
  from accepted_with_bound_tables_imp_accepted[OF bound]
  obtain result final_state where out_eq: "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  show ?thesis
  proof (cases "hash_map_output_collision final_state")
    case True
    then have "hash_map_output_collision_bad s out"
      unfolding hash_map_output_collision_bad_def accepted_def out_eq by simp
    then show ?thesis by simp
  next
    case clean: False
    have header_ex:
      "\<exists>fr f_fri_roots f_final header_as composition_fri_roots final rest.
        verifier_header_transcript s fr f_fri_roots f_final header_as dg
          composition_fri_roots final rest"
    proof -
      from challenges[unfolded accepted_fri_challenges_def] show ?thesis
      proof (elim exE conjE)
        fix result0 final_state0 fr0 f_fl0 f_final0 as0 fl0 final0
          query_state0
        assume
          header0:
            "verifier_header_transcript s fr0 (map snd f_fl0) f_final0 as0 dg
              (map snd fl0) final0 (PTranscript query_state0)"
        show ?thesis
          apply (rule exI[where x=fr0])
          apply (rule exI[where x="map snd f_fl0"])
          apply (rule exI[where x=f_final0])
          apply (rule exI[where x=as0])
          apply (rule exI[where x="map snd fl0"])
          apply (rule exI[where x=final0])
          apply (rule exI[where x="PTranscript query_state0"])
          apply (rule header0)
          done
      qed
    qed
    then obtain fr f_fri_roots f_final header_as composition_fri_roots final
        rest where
      header:
        "verifier_header_transcript s fr f_fri_roots f_final header_as dg
          composition_fri_roots final rest"
      by blast
    from bound obtain fr' f_fri_roots' f_final' dg'
        composition_fri_roots' final' rest' where
      header_bound:
        "verifier_header_transcript s fr' f_fri_roots' f_final' as dg'
          composition_fri_roots' final' rest'"
      and bind:
        "merkle_root_binds_table fr' trace_table final_state"
      unfolding accepted_with_bound_tables_def out_eq by blast
    have fr_eq: "fr' = fr"
      using verifier_header_transcript_unique[OF header_bound header] by simp
    have outcome_some:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
      using outcome out_eq by simp
    have bound_some:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
      using bound out_eq by simp
    have challenges_some:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
        comp_bs"
      using challenges out_eq by simp
    have bind_fr: "merkle_root_binds_table fr trace_table final_state"
      using bind fr_eq by simp
    have state:
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
      unfolding trace_fri_supported_root_trace_table_candidate_state_def
      using outcome_some bound_some challenges_some header bind_fr by blast
    have candidate:
      "trace_table \<in>
        trace_fri_supported_root_partial_trace_table_candidates s fr"
      by (rule
          trace_fri_supported_root_trace_table_candidate_state_imp_partial_candidate
          [OF state clean])
    have trace_bs_space:
      "trace_bs \<in> fri_challenge_space (ceil_log clength)"
      by (rule accepted_fri_challenges_trace_space[OF challenges])
    have trace_bs_union:
      "trace_bs \<in>
        trace_fri_supported_root_partial_union_bad_sets s bad_sets fr"
      unfolding trace_fri_supported_root_partial_union_bad_sets_def
      using trace_bs_space candidate trace_bs_bad by blast
    show ?thesis
      unfolding trace_fri_root_list_set_hit_def
      using challenges header trace_bs_union by blast
  qed
qed

lemma alpha_bad_set_hit_imp_partial_union_or_collision:
  assumes outcome: "out \<in> set_dist (execute verify_monad s)"
    and hit: "alpha_bad_set_hit s bad_sets out"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
  shows
    "alpha_header_list_set_hit s
      (alpha_header_supported_partial_union_bad_sets s bad_sets) out \<or>
     hash_map_output_collision_bad s out"
proof -
  from hit obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table
        as query_idxs"
    and as_bad: "as \<in> bad_sets trace_table"
    unfolding alpha_bad_set_hit_def by blast
  from accepted_with_bound_tables_imp_accepted[OF bound]
  obtain result final_state where out_eq: "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  show ?thesis
  proof (cases "hash_map_output_collision final_state")
    case True
    then have "hash_map_output_collision_bad s out"
      unfolding hash_map_output_collision_bad_def accepted_def out_eq by simp
    then show ?thesis by simp
  next
    case clean: False
    from bound obtain fr f_fri_roots f_final dg composition_fri_roots final
        rest where
      header:
        "verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest"
      and bind:
        "merkle_root_binds_table fr trace_table final_state"
      unfolding accepted_with_bound_tables_def out_eq by blast
    have shape:
      "accepted_transcript_shape s out as query_idxs"
      using accepted_with_bound_tables_imp_accepted_with_tables[OF bound]
        accepted_with_tables_imp_accepted_transcript_shape
      by blast
    have state:
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
      unfolding alpha_header_supported_trace_table_candidate_state_def
      by (intro exI[of _ result] exI[of _ composition_table]
          exI[of _ as] exI[of _ query_idxs] exI[of _ dg]
          exI[of _ composition_fri_roots] exI[of _ final]
          exI[of _ rest])
        (use outcome out_eq bound header bind in simp)
    have candidate:
      "trace_table \<in>
        alpha_header_supported_partial_trace_table_candidates s fr
          f_fri_roots f_final"
      by (rule
          alpha_header_supported_trace_table_candidate_state_imp_partial_candidate
          [OF state clean])
    have as_union:
      "as \<in>
        alpha_header_supported_partial_union_bad_sets s bad_sets fr
          f_fri_roots f_final"
      unfolding alpha_header_supported_partial_union_bad_sets_def
      using as_bad candidate subset[of trace_table] by auto
    show ?thesis
      unfolding alpha_header_list_set_hit_def
      using shape out_eq header as_union by blast
  qed
qed

lemma wp_trace_fri_challenge_set_hit_bound_via_partial_union_or_collision:
  fixes C H :: prob
  assumes partial_bound:
      "wp_event verify_monad
        (trace_fri_root_list_set_hit s
          (trace_fri_supported_root_partial_union_bad_sets s bad_sets)) s \<le> C"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le>
      C + H"
proof -
  have mono:
    "wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_root_list_set_hit s
            (trace_fri_supported_root_partial_union_bad_sets s bad_sets) out \<or>
          hash_map_output_collision_bad s out) s"
    by (rule wp_event_mono_on_support)
      (use trace_fri_challenge_set_hit_imp_partial_union_or_collision in blast)
  also have "... \<le> C + H"
  proof -
    have "wp_event verify_monad
        (\<lambda>out.
          trace_fri_root_list_set_hit s
            (trace_fri_supported_root_partial_union_bad_sets s bad_sets) out \<or>
          hash_map_output_collision_bad s out) s \<le>
        wp_event verify_monad
          (trace_fri_root_list_set_hit s
            (trace_fri_supported_root_partial_union_bad_sets s bad_sets)) s +
        wp_event verify_monad (hash_map_output_collision_bad s) s"
      by (rule wp_event_union_bound)
    also have "... \<le> C + H"
      by (intro add_mono partial_bound collision_bound)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma accepted_verifier_initial_imp_transcript_target_hit_on_support:
  assumes support:
      "out \<in> set_dist (execute verify_monad (verifier_initial_state tr))"
    and acc: "accepted out"
  shows "hash_new_output_hit_event (set tr) (verifier_initial_state tr) out"
proof -
  from acc obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  have outcome:
    "Some (result, final_state) \<in>
      set_dist (execute verify_monad (verifier_initial_state tr))"
    using support out_eq by simp
  have hit:
    "hash_map_new_output_hit (set tr) (verifier_initial_state tr)
      final_state"
    by (rule verify_monad_verifier_initial_trace_root_target_hit[OF outcome])
  show ?thesis
    unfolding hash_new_output_hit_event_def out_eq
    using hit by simp
qed

lemma wp_alpha_bad_set_hit_bound_via_partial_union_or_collision:
  fixes C H :: prob
  assumes subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and partial_bound:
      "wp_event verify_monad
        (alpha_header_list_set_hit s
          (alpha_header_supported_partial_union_bad_sets s bad_sets)) s \<le> C"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (alpha_bad_set_hit s bad_sets) s \<le> C + H"
proof -
  have mono:
    "wp_event verify_monad (alpha_bad_set_hit s bad_sets) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          alpha_header_list_set_hit s
            (alpha_header_supported_partial_union_bad_sets s bad_sets) out \<or>
          hash_map_output_collision_bad s out) s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute verify_monad s)"
      and hit: "alpha_bad_set_hit s bad_sets out"
    show
      "alpha_header_list_set_hit s
        (alpha_header_supported_partial_union_bad_sets s bad_sets) out \<or>
       hash_map_output_collision_bad s out"
      by (rule alpha_bad_set_hit_imp_partial_union_or_collision
          [OF support hit subset])
  qed
  also have "... \<le> C + H"
  proof -
    have "wp_event verify_monad
        (\<lambda>out.
          alpha_header_list_set_hit s
            (alpha_header_supported_partial_union_bad_sets s bad_sets) out \<or>
          hash_map_output_collision_bad s out) s \<le>
        wp_event verify_monad
          (alpha_header_list_set_hit s
            (alpha_header_supported_partial_union_bad_sets s bad_sets)) s +
        wp_event verify_monad (hash_map_output_collision_bad s) s"
      by (rule wp_event_union_bound)
    also have "... \<le> C + H"
      by (intro add_mono partial_bound collision_bound)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma wp_trace_fri_challenge_set_hit_bound_via_supported_partial_union_or_collision:
  fixes C H :: prob
  assumes future: "trace_fri_future_fresh s"
    and union_bound:
      "\<And>fr. nnreal
        (card (trace_fri_supported_root_partial_union_bad_sets s bad_sets fr)) /
        nnreal (CARD('f) ^ ceil_log clength) \<le> C"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le>
      C + H"
proof -
  have partial_bound:
    "wp_event verify_monad
      (trace_fri_root_list_set_hit s
        (trace_fri_supported_root_partial_union_bad_sets s bad_sets)) s \<le> C"
    by (rule wp_verify_monad_trace_fri_root_list_set_bound[OF future])
      (use trace_fri_supported_root_partial_union_bad_sets_subset union_bound
        in simp_all)
  show ?thesis
    by (rule wp_trace_fri_challenge_set_hit_bound_via_partial_union_or_collision
        [OF partial_bound collision_bound])
qed

lemma wp_alpha_bad_set_hit_bound_via_supported_partial_union_or_collision:
  fixes C H :: prob
  assumes future: "alpha_future_fresh s"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and union_bound:
      "\<And>fr f_fri_roots f_final.
        nnreal
          (card
            (alpha_header_supported_partial_union_bad_sets s bad_sets fr
              f_fri_roots f_final)) /
          nnreal (card alpha_space) \<le> C"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows "wp_event verify_monad (alpha_bad_set_hit s bad_sets) s \<le> C + H"
proof -
  have partial_bound:
    "wp_event verify_monad
      (alpha_header_list_set_hit s
        (alpha_header_supported_partial_union_bad_sets s bad_sets)) s \<le> C"
    by (rule wp_verify_monad_alpha_header_list_set_bound[OF future])
      (use alpha_header_supported_partial_union_bad_sets_subset_alpha_space
        union_bound in simp_all)
  show ?thesis
    by (rule wp_alpha_bad_set_hit_bound_via_partial_union_or_collision
        [OF subset partial_bound collision_bound])
qed

lemma trace_fri_supported_root_partial_union_bad_sets_fraction_bound_if_unique_candidate:
  fixes C :: prob
  assumes unique:
      "\<exists>trace_table.
        trace_fri_supported_root_partial_trace_table_candidates s fr \<subseteq>
          {trace_table}"
    and subset:
      "\<And>trace_table. bad_sets trace_table \<subseteq>
        fri_challenge_space (ceil_log clength)"
    and bound:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) /
          nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "nnreal
      (card (trace_fri_supported_root_partial_union_bad_sets s bad_sets fr)) /
      nnreal (CARD('f) ^ ceil_log clength) \<le> C"
proof -
  from unique obtain trace_table where candidates:
    "trace_fri_supported_root_partial_trace_table_candidates s fr \<subseteq>
      {trace_table}"
    by blast
  have union_subset:
    "trace_fri_supported_root_partial_union_bad_sets s bad_sets fr \<subseteq>
      bad_sets trace_table"
    unfolding trace_fri_supported_root_partial_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (bad_sets trace_table)"
    by (rule finite_subset[OF subset finite_fri_challenge_space])
  have card_le:
    "card (trace_fri_supported_root_partial_union_bad_sets s bad_sets fr) \<le>
      card (bad_sets trace_table)"
    by (rule card_mono[OF finite_bad union_subset])
  have "nnreal
        (card
          (trace_fri_supported_root_partial_union_bad_sets s bad_sets fr)) /
      nnreal (CARD('f) ^ ceil_log clength) \<le>
      nnreal (card (bad_sets trace_table)) /
        nnreal (CARD('f) ^ ceil_log clength)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

end

end
