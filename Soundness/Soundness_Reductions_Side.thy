(*  Title:      Stark/Soundness_Reductions_Side.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Reductions_Side
  imports Soundness_Reductions_Composition
begin

text \<open>Supported pairwise/output-local side-event reductions.\<close>

context soundness
begin

text \<open>
  The following cross-continuation predicates are retained temporarily as a
  record of the earlier proof route.  The refined route below does not charge
  same-key/different-output lazy-oracle continuations as bad events; it uses
  \<^term>\<open>supported_output_local_side_bad\<close> instead.
\<close>

definition supported_pairwise_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "supported_pairwise_merkle_bad s \<longleftrightarrow>
      alpha_supported_pairwise_merkle_bad s \<or>
      query_supported_pairwise_merkle_bad s \<or>
      trace_fri_supported_pairwise_merkle_bad s \<or>
      composition_fri_supported_pairwise_merkle_bad s"

definition supported_pairwise_coupling_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "supported_pairwise_coupling_bad s \<longleftrightarrow>
      alpha_supported_pairwise_coupling_bad s \<or>
      query_supported_pairwise_coupling_bad s \<or>
      trace_fri_supported_pairwise_coupling_bad s \<or>
      composition_fri_supported_pairwise_coupling_bad s"

lemma supported_pairwise_merkle_bad_imp_supported_hash_collision_possible_or_coupling_bad:
  assumes bad: "supported_pairwise_merkle_bad s"
  shows
    "supported_hash_output_collision_possible s \<or>
     supported_pairwise_coupling_bad s"
  using assms
  unfolding supported_pairwise_merkle_bad_def
    supported_pairwise_coupling_bad_def
  using
    alpha_supported_pairwise_merkle_bad_imp_supported_hash_collision_possible_or_coupling_bad
    query_supported_pairwise_merkle_bad_imp_supported_hash_collision_possible_or_coupling_bad
    trace_fri_supported_pairwise_merkle_bad_imp_supported_hash_collision_possible_or_coupling_bad
    composition_fri_supported_pairwise_merkle_bad_imp_supported_hash_collision_possible_or_coupling_bad
  by blast

lemma no_supported_pairwise_merkle_bad_if_no_hash_collision_possible_no_coupling_bad:
  assumes no_collision: "\<not> supported_hash_output_collision_possible s"
    and no_coupling: "\<not> supported_pairwise_coupling_bad s"
  shows "\<not> supported_pairwise_merkle_bad s"
proof
  assume bad: "supported_pairwise_merkle_bad s"
  have "supported_hash_output_collision_possible s \<or>
      supported_pairwise_coupling_bad s"
    by (rule
        supported_pairwise_merkle_bad_imp_supported_hash_collision_possible_or_coupling_bad
        [OF bad])
  then show False
    using no_collision no_coupling by blast
qed

lemma no_alpha_supported_pairwise_merkle_bad_if_no_pairwise_side_bad:
  assumes no_collision: "\<not> supported_hash_output_collision_possible s"
    and no_coupling: "\<not> supported_pairwise_coupling_bad s"
  shows "\<not> alpha_supported_pairwise_merkle_bad s"
proof -
  have "\<not> supported_pairwise_merkle_bad s"
    by (rule
        no_supported_pairwise_merkle_bad_if_no_hash_collision_possible_no_coupling_bad
        [OF no_collision no_coupling])
  then show ?thesis
    unfolding supported_pairwise_merkle_bad_def by blast
qed

lemma no_query_supported_pairwise_merkle_bad_if_no_pairwise_side_bad:
  assumes no_collision: "\<not> supported_hash_output_collision_possible s"
    and no_coupling: "\<not> supported_pairwise_coupling_bad s"
  shows "\<not> query_supported_pairwise_merkle_bad s"
proof -
  have "\<not> supported_pairwise_merkle_bad s"
    by (rule
        no_supported_pairwise_merkle_bad_if_no_hash_collision_possible_no_coupling_bad
        [OF no_collision no_coupling])
  then show ?thesis
    unfolding supported_pairwise_merkle_bad_def by blast
qed

lemma no_trace_fri_supported_pairwise_merkle_bad_if_no_pairwise_side_bad:
  assumes no_collision: "\<not> supported_hash_output_collision_possible s"
    and no_coupling: "\<not> supported_pairwise_coupling_bad s"
  shows "\<not> trace_fri_supported_pairwise_merkle_bad s"
proof -
  have "\<not> supported_pairwise_merkle_bad s"
    by (rule
        no_supported_pairwise_merkle_bad_if_no_hash_collision_possible_no_coupling_bad
        [OF no_collision no_coupling])
  then show ?thesis
    unfolding supported_pairwise_merkle_bad_def by blast
qed

lemma no_composition_fri_supported_pairwise_merkle_bad_if_no_pairwise_side_bad:
  assumes no_collision: "\<not> supported_hash_output_collision_possible s"
    and no_coupling: "\<not> supported_pairwise_coupling_bad s"
  shows "\<not> composition_fri_supported_pairwise_merkle_bad s"
proof -
  have "\<not> supported_pairwise_merkle_bad s"
    by (rule
        no_supported_pairwise_merkle_bad_if_no_hash_collision_possible_no_coupling_bad
        [OF no_collision no_coupling])
  then show ?thesis
    unfolding supported_pairwise_merkle_bad_def by blast
qed

definition alpha_supported_pairwise_coupling_event
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "alpha_supported_pairwise_coupling_event s out \<longleftrightarrow>
      (\<exists>result final_state fr f_fri_roots f_final trace_table
          trace_table' final_state'.
        out = Some (result, final_state) \<and>
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table final_state \<and>
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table' final_state' \<and>
        trace_table \<noteq> trace_table' \<and>
        merkle_hash_pairwise_coupling_bad final_state final_state')"

definition query_supported_pairwise_coupling_event
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_supported_pairwise_coupling_event s out \<longleftrightarrow>
      (\<exists>result final_state fr f_fri_roots f_final as dg
          composition_fri_roots final trace_table composition_table
          trace_table' composition_table' final_state'.
        out = Some (result, final_state) \<and>
        query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table composition_table
          final_state \<and>
        query_header_supported_table_candidate_state s fr f_fri_roots f_final
          as dg composition_fri_roots final trace_table' composition_table'
          final_state' \<and>
        (trace_table \<noteq> trace_table' \<or>
         composition_table \<noteq> composition_table') \<and>
        merkle_hash_pairwise_coupling_bad final_state final_state')"

definition trace_fri_supported_pairwise_coupling_event
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_supported_pairwise_coupling_event s out \<longleftrightarrow>
      (\<exists>result final_state fr trace_table trace_table' final_state'.
        out = Some (result, final_state) \<and>
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table
          final_state \<and>
        trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
          final_state' \<and>
        trace_table \<noteq> trace_table' \<and>
        merkle_hash_pairwise_coupling_bad final_state final_state')"

definition composition_fri_supported_pairwise_coupling_event
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_fri_supported_pairwise_coupling_event s out \<longleftrightarrow>
      (\<exists>result final_state fr f_fri_roots f_final as dg
          composition_fri_roots composition_table composition_table'
          final_state'.
        out = Some (result, final_state) \<and>
        composition_fri_supported_root_composition_table_candidate_state s fr
          f_fri_roots f_final as dg composition_fri_roots composition_table
          final_state \<and>
        composition_fri_supported_root_composition_table_candidate_state s fr
          f_fri_roots f_final as dg composition_fri_roots composition_table'
          final_state' \<and>
        composition_table \<noteq> composition_table' \<and>
        merkle_hash_pairwise_coupling_bad final_state final_state')"

definition supported_pairwise_coupling_event
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "supported_pairwise_coupling_event s out \<longleftrightarrow>
      alpha_supported_pairwise_coupling_event s out \<or>
      query_supported_pairwise_coupling_event s out \<or>
      trace_fri_supported_pairwise_coupling_event s out \<or>
      composition_fri_supported_pairwise_coupling_event s out"

definition supported_pairwise_side_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "supported_pairwise_side_bad s out \<longleftrightarrow>
      hash_map_output_collision_bad s out \<or>
      supported_pairwise_coupling_event s out"

lemma alpha_supported_pairwise_coupling_event_imp_accepted:
  assumes "alpha_supported_pairwise_coupling_event s out"
  shows "accepted out"
  using assms
  unfolding alpha_supported_pairwise_coupling_event_def accepted_def
  by auto

lemma query_supported_pairwise_coupling_event_imp_accepted:
  assumes "query_supported_pairwise_coupling_event s out"
  shows "accepted out"
  using assms
  unfolding query_supported_pairwise_coupling_event_def accepted_def
  by auto

lemma trace_fri_supported_pairwise_coupling_event_imp_accepted:
  assumes "trace_fri_supported_pairwise_coupling_event s out"
  shows "accepted out"
  using assms
  unfolding trace_fri_supported_pairwise_coupling_event_def accepted_def
  by auto

lemma composition_fri_supported_pairwise_coupling_event_imp_accepted:
  assumes "composition_fri_supported_pairwise_coupling_event s out"
  shows "accepted out"
  using assms
  unfolding composition_fri_supported_pairwise_coupling_event_def accepted_def
  by auto

lemma supported_pairwise_coupling_event_imp_accepted:
  assumes "supported_pairwise_coupling_event s out"
  shows "accepted out"
  using assms
  unfolding supported_pairwise_coupling_event_def
  using alpha_supported_pairwise_coupling_event_imp_accepted
    query_supported_pairwise_coupling_event_imp_accepted
    trace_fri_supported_pairwise_coupling_event_imp_accepted
    composition_fri_supported_pairwise_coupling_event_imp_accepted
  by blast

lemma supported_pairwise_side_bad_imp_accepted:
  assumes "supported_pairwise_side_bad s out"
  shows "accepted out"
  using assms
  unfolding supported_pairwise_side_bad_def
  using hash_map_output_collision_bad_imp_accepted
    supported_pairwise_coupling_event_imp_accepted
  by blast

lemma supported_pairwise_side_bad_mono_accepted:
  "wp_event verify_monad (supported_pairwise_side_bad s) s \<le>
    wp_event verify_monad accepted s"
  by (rule wp_event_mono)
    (rule supported_pairwise_side_bad_imp_accepted)

lemma supported_pairwise_side_bad_union_bound:
  fixes hash_error coupling_error :: prob
  assumes hash_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le>
        hash_error"
    and coupling_bound:
      "wp_event verify_monad (supported_pairwise_coupling_event s) s \<le>
        coupling_error"
  shows
    "wp_event verify_monad (supported_pairwise_side_bad s) s \<le>
      hash_error + coupling_error"
proof -
  have "wp_event verify_monad (supported_pairwise_side_bad s) s \<le>
      wp_event verify_monad (hash_map_output_collision_bad s) s +
      wp_event verify_monad (supported_pairwise_coupling_event s) s"
    unfolding supported_pairwise_side_bad_def
      supported_pairwise_coupling_event_def
    by (rule wp_event_union_bound)
  also have "... \<le> hash_error + coupling_error"
    by (intro add_mono hash_bound coupling_bound)
  finally show ?thesis .
qed

lemma verifier_initial_hash_map_output_collision_bad_bound_concrete:
  "wp_event verify_monad
    (hash_map_output_collision_bad (verifier_initial_state tr))
    (verifier_initial_state tr) \<le> concrete_merkle_binding_error"
proof -
  let ?s = "verifier_initial_state tr"
  have "wp_event verify_monad (hash_map_output_collision_bad ?s) ?s \<le>
      wp_event verify_monad (hash_map_new_output_collision_bad ?s) ?s"
    by (rule wp_event_mono)
      (rule hash_map_output_collision_bad_imp_new_collision_bad_if_initial_clean,
        simp, assumption)
  also have "... \<le> concrete_merkle_binding_error"
    by (rule verifier_initial_hash_map_new_output_collision_bad_bound_concrete)
  finally show ?thesis .
qed

lemma verifier_initial_supported_output_local_candidate_ambiguity_bad_bound_concrete:
  "wp_event verify_monad
      (supported_output_local_candidate_ambiguity_bad
        (verifier_initial_state tr))
      (verifier_initial_state tr) \<le>
    concrete_merkle_binding_error"
proof -
  have "wp_event verify_monad
      (supported_output_local_candidate_ambiguity_bad
        (verifier_initial_state tr))
      (verifier_initial_state tr) \<le>
    wp_event verify_monad
      (hash_map_output_collision_bad (verifier_initial_state tr))
      (verifier_initial_state tr)"
    by (rule
        supported_output_local_candidate_ambiguity_bad_mono_hash_map_output_collision_bad)
  also have "... \<le> concrete_merkle_binding_error"
    by (rule verifier_initial_hash_map_output_collision_bad_bound_concrete)
  finally show ?thesis .
qed

lemma verifier_initial_supported_output_local_side_bad_bound_concrete:
  "wp_event verify_monad
      (supported_output_local_side_bad (verifier_initial_state tr))
      (verifier_initial_state tr) \<le>
    concrete_merkle_binding_error"
  unfolding supported_output_local_side_bad_iff_hash_map_output_collision_bad
  by (rule verifier_initial_hash_map_output_collision_bad_bound_concrete)

lemma verifier_initial_supported_pairwise_side_bad_bound_if_coupling_event_bound:
  assumes coupling_bound:
      "wp_event verify_monad
        (supported_pairwise_coupling_event (verifier_initial_state tr))
        (verifier_initial_state tr) \<le> coupling_error"
  shows
    "wp_event verify_monad
      (supported_pairwise_side_bad (verifier_initial_state tr))
      (verifier_initial_state tr) \<le>
      concrete_merkle_binding_error + coupling_error"
  by (rule supported_pairwise_side_bad_union_bound
      [OF verifier_initial_hash_map_output_collision_bad_bound_concrete
        coupling_bound])

lemma supported_hash_output_collision_possible_imp_exists_supported_pairwise_side_bad:
  assumes "supported_hash_output_collision_possible s"
  shows "\<exists>out \<in> set_dist (execute verify_monad s).
    supported_pairwise_side_bad s out"
  using assms
  unfolding supported_hash_output_collision_possible_def
    supported_pairwise_side_bad_def
  by blast

lemma alpha_supported_pairwise_coupling_bad_imp_exists_supported_pairwise_side_bad:
  assumes alpha_bad: "alpha_supported_pairwise_coupling_bad s"
  shows "\<exists>out \<in> set_dist (execute verify_monad s).
    supported_pairwise_side_bad s out"
proof -
  from alpha_bad obtain fr f_fri_roots f_final trace_table final_state
      trace_table' final_state' where
    candidate:
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
    and candidate':
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table' final_state'"
    and distinct: "trace_table \<noteq> trace_table'"
    and pair_bad:
      "merkle_hash_pairwise_coupling_bad final_state final_state'"
    unfolding alpha_supported_pairwise_coupling_bad_def
      alpha_header_supported_pairwise_coupling_bad_def
    by blast
  from candidate obtain result composition_table as query_idxs dg
      composition_fri_roots final rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    unfolding alpha_header_supported_trace_table_candidate_state_def by blast
  have coupling:
    "supported_pairwise_coupling_event s (Some (result, final_state))"
    unfolding supported_pairwise_coupling_event_def
      alpha_supported_pairwise_coupling_event_def
    using candidate candidate' distinct pair_bad by blast
  have side:
    "supported_pairwise_side_bad s (Some (result, final_state))"
    unfolding supported_pairwise_side_bad_def
    using coupling by simp
  show ?thesis
    using outcome side by blast
qed

lemma query_supported_pairwise_coupling_bad_imp_exists_supported_pairwise_side_bad:
  assumes query_bad: "query_supported_pairwise_coupling_bad s"
  shows "\<exists>out \<in> set_dist (execute verify_monad s).
    supported_pairwise_side_bad s out"
proof -
  from query_bad obtain fr f_fri_roots f_final as dg composition_fri_roots
      final trace_table composition_table final_state trace_table'
      composition_table' final_state' where
    candidate:
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table composition_table
        final_state"
    and candidate':
      "query_header_supported_table_candidate_state s fr f_fri_roots f_final
        as dg composition_fri_roots final trace_table' composition_table'
        final_state'"
    and distinct:
      "trace_table \<noteq> trace_table' \<or>
       composition_table \<noteq> composition_table'"
    and pair_bad:
      "merkle_hash_pairwise_coupling_bad final_state final_state'"
    unfolding query_supported_pairwise_coupling_bad_def
      query_header_supported_pairwise_coupling_bad_def
    by blast
  from candidate obtain result query_idxs rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    unfolding query_header_supported_table_candidate_state_def by blast
  have coupling:
    "supported_pairwise_coupling_event s (Some (result, final_state))"
    unfolding supported_pairwise_coupling_event_def
      query_supported_pairwise_coupling_event_def
    using candidate candidate' distinct pair_bad by blast
  have side:
    "supported_pairwise_side_bad s (Some (result, final_state))"
    unfolding supported_pairwise_side_bad_def
    using coupling by simp
  show ?thesis
    using outcome side by blast
qed

lemma trace_fri_supported_pairwise_coupling_bad_imp_exists_supported_pairwise_side_bad:
  assumes trace_bad: "trace_fri_supported_pairwise_coupling_bad s"
  shows "\<exists>out \<in> set_dist (execute verify_monad s).
    supported_pairwise_side_bad s out"
proof -
  from trace_bad obtain fr trace_table final_state trace_table' final_state'
    where candidate:
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table
        final_state"
    and candidate':
      "trace_fri_supported_root_trace_table_candidate_state s fr trace_table'
        final_state'"
    and distinct: "trace_table \<noteq> trace_table'"
    and pair_bad:
      "merkle_hash_pairwise_coupling_bad final_state final_state'"
    unfolding trace_fri_supported_pairwise_coupling_bad_def
      trace_fri_supported_root_pairwise_coupling_bad_def
    by blast
  from candidate obtain result composition_table as query_idxs trace_bs dg
      comp_bs f_fri_roots f_final header_as composition_fri_roots final rest
    where outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    unfolding trace_fri_supported_root_trace_table_candidate_state_def
    by blast
  have coupling:
    "supported_pairwise_coupling_event s (Some (result, final_state))"
    unfolding supported_pairwise_coupling_event_def
      trace_fri_supported_pairwise_coupling_event_def
    using candidate candidate' distinct pair_bad by blast
  have side:
    "supported_pairwise_side_bad s (Some (result, final_state))"
    unfolding supported_pairwise_side_bad_def
    using coupling by simp
  show ?thesis
    using outcome side by blast
qed

lemma composition_fri_supported_pairwise_coupling_bad_imp_exists_supported_pairwise_side_bad:
  assumes composition_bad: "composition_fri_supported_pairwise_coupling_bad s"
  shows "\<exists>out \<in> set_dist (execute verify_monad s).
    supported_pairwise_side_bad s out"
proof -
  from composition_bad obtain fr f_fri_roots f_final as dg
      composition_fri_roots composition_table final_state composition_table'
      final_state' where
    candidate:
      "composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table
        final_state"
    and candidate':
      "composition_fri_supported_root_composition_table_candidate_state s fr
        f_fri_roots f_final as dg composition_fri_roots composition_table'
        final_state'"
    and distinct: "composition_table \<noteq> composition_table'"
    and pair_bad:
      "merkle_hash_pairwise_coupling_bad final_state final_state'"
    unfolding composition_fri_supported_pairwise_coupling_bad_def
      composition_fri_supported_root_pairwise_coupling_bad_def
    by blast
  from candidate obtain result trace_table query_idxs trace_bs comp_bs final
      rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    unfolding
      composition_fri_supported_root_composition_table_candidate_state_def
    by blast
  have coupling:
    "supported_pairwise_coupling_event s (Some (result, final_state))"
    unfolding supported_pairwise_coupling_event_def
      composition_fri_supported_pairwise_coupling_event_def
    using candidate candidate' distinct pair_bad by blast
  have side:
    "supported_pairwise_side_bad s (Some (result, final_state))"
    unfolding supported_pairwise_side_bad_def
    using coupling by simp
  show ?thesis
    using outcome side by blast
qed

lemma supported_pairwise_coupling_bad_imp_exists_supported_pairwise_side_bad:
  assumes coupling: "supported_pairwise_coupling_bad s"
  shows "\<exists>out \<in> set_dist (execute verify_monad s).
    supported_pairwise_side_bad s out"
  using coupling
  unfolding supported_pairwise_coupling_bad_def
  using
    alpha_supported_pairwise_coupling_bad_imp_exists_supported_pairwise_side_bad
    query_supported_pairwise_coupling_bad_imp_exists_supported_pairwise_side_bad
    trace_fri_supported_pairwise_coupling_bad_imp_exists_supported_pairwise_side_bad
    composition_fri_supported_pairwise_coupling_bad_imp_exists_supported_pairwise_side_bad
  by blast

lemma supported_pairwise_merkle_bad_imp_exists_supported_pairwise_side_bad:
  assumes bad: "supported_pairwise_merkle_bad s"
  shows "\<exists>out \<in> set_dist (execute verify_monad s).
    supported_pairwise_side_bad s out"
proof -
  have side:
    "supported_hash_output_collision_possible s \<or>
     supported_pairwise_coupling_bad s"
    by (rule
        supported_pairwise_merkle_bad_imp_supported_hash_collision_possible_or_coupling_bad
        [OF bad])
  then show ?thesis
  proof
    assume "supported_hash_output_collision_possible s"
    then show ?thesis
      by (rule
          supported_hash_output_collision_possible_imp_exists_supported_pairwise_side_bad)
  next
    assume "supported_pairwise_coupling_bad s"
    then show ?thesis
      by (rule
          supported_pairwise_coupling_bad_imp_exists_supported_pairwise_side_bad)
  qed
qed

lemma no_supported_pairwise_side_bad_on_support_imp_no_hash_collision_possible:
  assumes no_side:
    "\<And>out. out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
      \<not> supported_pairwise_side_bad s out"
  shows "\<not> supported_hash_output_collision_possible s"
proof
  assume possible: "supported_hash_output_collision_possible s"
  from supported_hash_output_collision_possible_imp_exists_supported_pairwise_side_bad
      [OF possible]
  obtain out where out:
      "out \<in> set_dist (execute verify_monad s)"
    and side: "supported_pairwise_side_bad s out"
    by blast
  show False
    using no_side[OF out] side by contradiction
qed

lemma no_supported_pairwise_side_bad_on_support_imp_no_coupling_bad:
  assumes no_side:
    "\<And>out. out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
      \<not> supported_pairwise_side_bad s out"
  shows "\<not> supported_pairwise_coupling_bad s"
proof
  assume coupling: "supported_pairwise_coupling_bad s"
  from supported_pairwise_coupling_bad_imp_exists_supported_pairwise_side_bad
      [OF coupling]
  obtain out where out:
      "out \<in> set_dist (execute verify_monad s)"
    and side: "supported_pairwise_side_bad s out"
    by blast
  show False
    using no_side[OF out] side by contradiction
qed

lemma no_supported_pairwise_side_bad_on_support_imp_no_pairwise_side_bad:
  assumes no_side:
    "\<And>out. out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
      \<not> supported_pairwise_side_bad s out"
  shows
    "\<not> supported_hash_output_collision_possible s"
    "\<not> supported_pairwise_coupling_bad s"
proof -
  show "\<not> supported_hash_output_collision_possible s"
    by (rule
        no_supported_pairwise_side_bad_on_support_imp_no_hash_collision_possible
          [OF no_side])
  show "\<not> supported_pairwise_coupling_bad s"
    by (rule
        no_supported_pairwise_side_bad_on_support_imp_no_coupling_bad
          [OF no_side])
qed

lemma composition_fri_supported_root_candidate_unique_if_no_pairwise_merkle_bad:
  assumes no_bad:
    "\<not> composition_fri_supported_root_pairwise_merkle_bad s fr f_fri_roots
      f_final as dg composition_fri_roots"
  shows
    "\<exists>composition_table.
      composition_fri_supported_root_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots \<subseteq>
        {composition_table}"
proof (rule ccontr)
  assume not_unique:
    "\<not> (\<exists>composition_table.
      composition_fri_supported_root_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots \<subseteq>
        {composition_table})"
  have "composition_fri_supported_root_pairwise_merkle_bad s fr f_fri_roots
      f_final as dg composition_fri_roots"
    using
      composition_fri_supported_root_composition_table_candidates_not_singleton_imp_pairwise_merkle_bad
        [OF not_unique]
    unfolding composition_fri_supported_root_pairwise_merkle_bad_def
    by blast
  then show False
    using no_bad by contradiction
qed

lemma composition_fri_supported_root_candidate_unique_if_no_global_pairwise_merkle_bad:
  assumes no_bad: "\<not> composition_fri_supported_pairwise_merkle_bad s"
  shows
    "\<exists>composition_table.
      composition_fri_supported_root_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots \<subseteq>
        {composition_table}"
proof (rule
    composition_fri_supported_root_candidate_unique_if_no_pairwise_merkle_bad)
  show
    "\<not> composition_fri_supported_root_pairwise_merkle_bad s fr f_fri_roots
      f_final as dg composition_fri_roots"
    using no_bad
    unfolding composition_fri_supported_pairwise_merkle_bad_def by blast
qed

definition composition_fri_supported_root_union_bad_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> 'f list set) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f list set"
  where
    "composition_fri_supported_root_union_bad_sets s bad_sets fr f_fri_roots
      f_final as dg composition_fri_roots =
      {comp_bs \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
        \<exists>composition_table \<in>
          composition_fri_supported_root_composition_table_candidates s fr
            f_fri_roots f_final as dg composition_fri_roots.
          comp_bs \<in> bad_sets dg composition_table}"

lemma composition_fri_supported_root_union_bad_sets_subset:
  "composition_fri_supported_root_union_bad_sets s bad_sets fr f_fri_roots
      f_final as dg composition_fri_roots \<subseteq>
    fri_challenge_space (ceil_log (to_nat dg + 1))"
  unfolding composition_fri_supported_root_union_bad_sets_def by auto

lemma composition_fri_challenge_set_hit_imp_supported_root_union_list_set_hit:
  assumes outcome: "out \<in> set_dist (execute verify_monad s)"
    and hit: "composition_fri_challenge_set_hit s bad_sets out"
  shows
    "composition_fri_root_list_set_hit s
      (composition_fri_supported_root_union_bad_sets s bad_sets) out"
proof -
  from hit obtain trace_table composition_table as query_idxs trace_bs dg comp_bs
    where bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and challenges: "accepted_fri_challenges s out trace_bs dg comp_bs"
    and comp_bs_bad: "comp_bs \<in> bad_sets dg composition_table"
    unfolding composition_fri_challenge_set_hit_def by blast
  from bound obtain result_b final_state_b fr f_fri_roots f_final dg_b
      composition_fri_roots final rest where
    header_bound:
      "verifier_header_transcript s fr f_fri_roots f_final as dg_b
        composition_fri_roots final rest"
    unfolding accepted_with_bound_tables_def by blast
  from challenges[unfolded accepted_fri_challenges_def]
  obtain result_c final_state_c fr_c f_fl_c f_final_c as_c fl_c final_c
      query_state_c where challenge_body:
    "out = Some (result_c, final_state_c) \<and>
     verifier_header_transcript s fr_c (map snd f_fl_c) f_final_c as_c dg
        (map snd fl_c) final_c (PTranscript query_state_c) \<and>
     PState query_state_c =
        verifier_header_state s fr_c (map snd f_fl_c) f_final_c as_c dg
          (map snd fl_c) final_c \<and>
     Some (result_c, final_state_c) \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr_c f_fl_c f_final_c as_c fl_c
              final_c)
            rounds)
          query_state_c) \<and>
     PQueryCounter query_state_c = PQueryCounter s \<and>
     trace_bs = map fst f_fl_c \<and>
     comp_bs = map fst fl_c \<and>
     (\<forall>i < length f_fl_c.
        fmlookup (HashMap query_state_c)
          (TraceFriChallenge (PTraceFriCounter s + i)
            (foldl concat (concat (PState s) fr_c)
              (take (Suc i) (map snd f_fl_c)))) =
          Some (fst (f_fl_c ! i))) \<and>
     (\<forall>i < length fl_c.
        fmlookup (HashMap query_state_c)
          (CompositionFriChallenge (PCompositionFriCounter s + i)
            (foldl concat
              (concat
                (foldl concat
                  (concat
                    (foldl concat (concat (PState s) fr_c)
                      (map snd f_fl_c))
                    f_final_c)
                  as_c)
                dg)
              (take (Suc i) (map snd fl_c)))) =
          Some (fst (fl_c ! i)))"
    by (elim exE)
  have out_challenges: "out = Some (result_c, final_state_c)"
    using challenge_body by simp
  have header_challenges:
    "verifier_header_transcript s fr_c (map snd f_fl_c) f_final_c as_c dg
      (map snd fl_c) final_c (PTranscript query_state_c)"
    using challenge_body by simp
  have dg_eq: "dg_b = dg"
    using verifier_header_transcript_unique[OF header_challenges header_bound]
    by simp
  have header:
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    using header_bound dg_eq by simp
  have candidate:
    "composition_table \<in>
      composition_fri_supported_root_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots"
    unfolding composition_fri_supported_root_composition_table_candidates_def
    using outcome bound challenges header by blast
  have comp_bs_space:
    "comp_bs \<in> fri_challenge_space (ceil_log (to_nat dg + 1))"
    by (rule accepted_fri_challenges_composition_space[OF challenges])
  have comp_bs_union:
    "comp_bs \<in>
      composition_fri_supported_root_union_bad_sets s bad_sets fr
        f_fri_roots f_final as dg composition_fri_roots"
    unfolding composition_fri_supported_root_union_bad_sets_def
    using comp_bs_space candidate comp_bs_bad by blast
  show ?thesis
    unfolding composition_fri_root_list_set_hit_def
    using challenges header comp_bs_union by blast
qed

lemma wp_composition_fri_challenge_set_hit_bound_via_supported_root_union:
  fixes C :: prob
  assumes future: "composition_fri_future_fresh s"
    and union_bound:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots.
        nnreal
          (card
            (composition_fri_supported_root_union_bad_sets s bad_sets fr
              f_fri_roots f_final as dg composition_fri_roots)) /
          nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad (composition_fri_challenge_set_hit s bad_sets) s \<le>
      C"
proof -
  have root_bound:
    "wp_event verify_monad
      (composition_fri_root_list_set_hit s
        (composition_fri_supported_root_union_bad_sets s bad_sets)) s \<le> C"
    by (rule wp_verify_monad_composition_fri_root_list_set_bound[OF future])
      (use composition_fri_supported_root_union_bad_sets_subset union_bound in
        simp_all)
  have "wp_event verify_monad (composition_fri_challenge_set_hit s bad_sets) s \<le>
      wp_event verify_monad
        (composition_fri_root_list_set_hit s
          (composition_fri_supported_root_union_bad_sets s bad_sets)) s"
    by (rule wp_event_mono_on_support)
      (rule composition_fri_challenge_set_hit_imp_supported_root_union_list_set_hit)
  also have "... \<le> C"
    by (rule root_bound)
  finally show ?thesis .
qed

lemma composition_fri_supported_root_union_bad_sets_fraction_bound_if_unique_candidate:
  fixes C :: prob
  assumes unique:
      "\<exists>composition_table.
        composition_fri_supported_root_composition_table_candidates s fr
          f_fri_roots f_final as dg composition_fri_roots \<subseteq>
          {composition_table}"
    and subset:
      "\<And>composition_table. bad_sets dg composition_table \<subseteq>
        fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>composition_table.
        nnreal (card (bad_sets dg composition_table)) /
          nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "nnreal
      (card
        (composition_fri_supported_root_union_bad_sets s bad_sets fr
          f_fri_roots f_final as dg composition_fri_roots)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
proof -
  from unique obtain composition_table where candidates:
    "composition_fri_supported_root_composition_table_candidates s fr
      f_fri_roots f_final as dg composition_fri_roots \<subseteq>
      {composition_table}"
    by blast
  have union_subset:
    "composition_fri_supported_root_union_bad_sets s bad_sets fr f_fri_roots
      f_final as dg composition_fri_roots \<subseteq>
      bad_sets dg composition_table"
    unfolding composition_fri_supported_root_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (bad_sets dg composition_table)"
    by (rule finite_subset[OF subset finite_fri_challenge_space])
  have card_le:
    "card
      (composition_fri_supported_root_union_bad_sets s bad_sets fr
        f_fri_roots f_final as dg composition_fri_roots) \<le>
      card (bad_sets dg composition_table)"
    by (rule card_mono[OF finite_bad union_subset])
  have "nnreal
        (card
          (composition_fri_supported_root_union_bad_sets s bad_sets fr
            f_fri_roots f_final as dg composition_fri_roots)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
      nnreal (card (bad_sets dg composition_table)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

definition composition_fri_supported_root_partial_union_bad_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> 'f list set) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f list set"
  where
    "composition_fri_supported_root_partial_union_bad_sets s bad_sets fr
      f_fri_roots f_final as dg composition_fri_roots =
      {comp_bs \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
        \<exists>composition_table \<in>
          composition_fri_supported_root_partial_composition_table_candidates
            s fr f_fri_roots f_final as dg composition_fri_roots.
          comp_bs \<in> bad_sets dg composition_table}"

lemma composition_fri_supported_root_partial_union_bad_sets_subset:
  "composition_fri_supported_root_partial_union_bad_sets s bad_sets fr
      f_fri_roots f_final as dg composition_fri_roots \<subseteq>
    fri_challenge_space (ceil_log (to_nat dg + 1))"
  unfolding composition_fri_supported_root_partial_union_bad_sets_def by auto

lemma composition_fri_supported_root_partial_union_bad_sets_fraction_bound_if_unique_candidate:
  fixes C :: prob
  assumes unique:
      "\<exists>composition_table.
        composition_fri_supported_root_partial_composition_table_candidates s
          fr f_fri_roots f_final as dg composition_fri_roots \<subseteq>
          {composition_table}"
    and subset:
      "\<And>composition_table. bad_sets dg composition_table \<subseteq>
        fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>composition_table.
        nnreal (card (bad_sets dg composition_table)) /
          nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "nnreal
      (card
        (composition_fri_supported_root_partial_union_bad_sets s bad_sets fr
          f_fri_roots f_final as dg composition_fri_roots)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
proof -
  from unique obtain composition_table where candidates:
    "composition_fri_supported_root_partial_composition_table_candidates s fr
      f_fri_roots f_final as dg composition_fri_roots \<subseteq>
      {composition_table}"
    by blast
  have union_subset:
    "composition_fri_supported_root_partial_union_bad_sets s bad_sets fr
      f_fri_roots f_final as dg composition_fri_roots \<subseteq>
      bad_sets dg composition_table"
    unfolding composition_fri_supported_root_partial_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (bad_sets dg composition_table)"
    by (rule finite_subset[OF subset finite_fri_challenge_space])
  have card_le:
    "card
      (composition_fri_supported_root_partial_union_bad_sets s bad_sets fr
        f_fri_roots f_final as dg composition_fri_roots) \<le>
      card (bad_sets dg composition_table)"
    by (rule card_mono[OF finite_bad union_subset])
  have "nnreal
        (card
          (composition_fri_supported_root_partial_union_bad_sets s bad_sets fr
            f_fri_roots f_final as dg composition_fri_roots)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
      nnreal (card (bad_sets dg composition_table)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma composition_fri_challenge_set_hit_imp_partial_union_or_collision:
  assumes outcome: "out \<in> set_dist (execute verify_monad s)"
    and hit: "composition_fri_challenge_set_hit s bad_sets out"
  shows
    "composition_fri_root_list_set_hit s
      (composition_fri_supported_root_partial_union_bad_sets s bad_sets) out \<or>
     hash_map_output_collision_bad s out"
proof -
  from hit obtain trace_table composition_table as query_idxs trace_bs dg comp_bs
    where bound:
        "accepted_with_bound_tables s out trace_table composition_table as
          query_idxs"
      and challenges: "accepted_fri_challenges s out trace_bs dg comp_bs"
      and trace_low: "trace_table_low_degree trace_table"
      and not_low:
        "\<not> composition_table_low_degree maxDegree composition_table"
      and comp_bs_bad: "comp_bs \<in> bad_sets dg composition_table"
    unfolding composition_fri_challenge_set_hit_def by blast
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
    from challenges obtain result_c final_state_c fr_c f_fl_c f_final_c as_c
        fl_c final_c query_state_c where
      out_c: "out = Some (result_c, final_state_c)"
      and
      header_challenges:
        "verifier_header_transcript s fr_c (map snd f_fl_c) f_final_c as_c dg
          (map snd fl_c) final_c (PTranscript query_state_c)"
      and query_state_c:
        "PState query_state_c =
          verifier_header_state s fr_c (map snd f_fl_c) f_final_c as_c dg
            (map snd fl_c) final_c"
      and query_out_c:
        "Some (result_c, final_state_c) \<in>
          set_dist
            (execute
              (ntimes
                (verifier_query_round_program fr_c f_fl_c f_final_c as_c fl_c
                  final_c) rounds)
              query_state_c)"
      and query_count_c:
        "PQueryCounter query_state_c = PQueryCounter s"
      and trace_eq_c: "trace_bs = map fst f_fl_c"
      and comp_eq_c: "comp_bs = map fst fl_c"
      and trace_lookup_c:
        "\<And>i. i < length f_fl_c \<Longrightarrow>
          fmlookup (HashMap query_state_c)
            (TraceFriChallenge (PTraceFriCounter s + i)
              (foldl concat (concat (PState s) fr_c)
                (take (Suc i) (map snd f_fl_c)))) =
          Some (fst (f_fl_c ! i))"
      and comp_lookup_c:
        "\<And>i. i < length fl_c \<Longrightarrow>
          fmlookup (HashMap query_state_c)
            (CompositionFriChallenge (PCompositionFriCounter s + i)
              (foldl concat
                (concat
                  (foldl concat
                    (concat
                      (foldl concat (concat (PState s) fr_c)
                        (map snd f_fl_c))
                      f_final_c)
                    as_c)
                  dg)
                (take (Suc i) (map snd fl_c)))) =
          Some (fst (fl_c ! i))"
      unfolding accepted_fri_challenges_def by blast
    from bound obtain fr_b f_fri_roots_b f_final_b dg_b
        composition_fri_roots_b final_b rest_b where
      header_bound:
        "verifier_header_transcript s fr_b f_fri_roots_b f_final_b as dg_b
          composition_fri_roots_b final_b rest_b"
      and comp_nonempty:
        "composition_fri_roots_b \<noteq> []"
      and comp_bind:
        "merkle_root_binds_table (hd composition_fri_roots_b) composition_table
          final_state"
      unfolding accepted_with_bound_tables_def out_eq by blast
    have dg_eq: "dg_b = dg"
      using verifier_header_transcript_unique
        [OF header_bound header_challenges]
      by simp
    have header:
      "verifier_header_transcript s fr_b f_fri_roots_b f_final_b as dg
        composition_fri_roots_b final_b rest_b"
      using header_bound dg_eq by simp
    have outcome_some:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
      using outcome out_eq by simp
    have bound_some:
      "accepted_with_bound_tables s (Some (result, final_state)) trace_table
        composition_table as query_idxs"
      using bound out_eq by simp
    have challenges_some:
      "accepted_fri_challenges s (Some (result, final_state)) trace_bs dg
        comp_bs"
      using challenges out_eq by simp
    have state:
      "composition_fri_supported_root_composition_table_candidate_state s
        fr_b f_fri_roots_b f_final_b as dg composition_fri_roots_b
        composition_table final_state"
      unfolding composition_fri_supported_root_composition_table_candidate_state_def
      using outcome_some bound_some challenges_some header comp_nonempty
        comp_bind
      by blast
    have candidate:
      "composition_table \<in>
        composition_fri_supported_root_partial_composition_table_candidates s
          fr_b f_fri_roots_b f_final_b as dg composition_fri_roots_b"
      using
        composition_fri_supported_root_composition_table_candidate_state_imp_partial_candidate_state
          [OF state clean]
        composition_fri_supported_root_partial_composition_table_candidates_iff_state
      by blast
    have comp_bs_space:
      "comp_bs \<in> fri_challenge_space (ceil_log (to_nat dg + 1))"
      by (rule accepted_fri_challenges_composition_space[OF challenges])
    have comp_bs_union:
      "comp_bs \<in>
        composition_fri_supported_root_partial_union_bad_sets s bad_sets
          fr_b f_fri_roots_b f_final_b as dg composition_fri_roots_b"
      unfolding composition_fri_supported_root_partial_union_bad_sets_def
      using comp_bs_space candidate comp_bs_bad by blast
    show ?thesis
      unfolding composition_fri_root_list_set_hit_def
      using challenges header comp_bs_union by blast
  qed
qed

lemma wp_composition_fri_challenge_set_hit_bound_via_partial_union_or_collision:
  fixes C H :: prob
  assumes partial_bound:
      "wp_event verify_monad
        (composition_fri_root_list_set_hit s
          (composition_fri_supported_root_partial_union_bad_sets s bad_sets))
        s \<le> C"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (composition_fri_challenge_set_hit s bad_sets) s \<le>
      C + H"
proof -
  have mono:
    "wp_event verify_monad (composition_fri_challenge_set_hit s bad_sets) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          composition_fri_root_list_set_hit s
            (composition_fri_supported_root_partial_union_bad_sets s bad_sets)
            out \<or>
          hash_map_output_collision_bad s out) s"
    by (rule wp_event_mono_on_support)
      (use composition_fri_challenge_set_hit_imp_partial_union_or_collision
        in blast)
  also have "... \<le> C + H"
  proof -
    have "wp_event verify_monad
        (\<lambda>out.
          composition_fri_root_list_set_hit s
            (composition_fri_supported_root_partial_union_bad_sets s bad_sets)
            out \<or>
          hash_map_output_collision_bad s out) s \<le>
        wp_event verify_monad
          (composition_fri_root_list_set_hit s
            (composition_fri_supported_root_partial_union_bad_sets s bad_sets))
          s +
        wp_event verify_monad (hash_map_output_collision_bad s) s"
      by (rule wp_event_union_bound)
    also have "... \<le> C + H"
      by (intro add_mono partial_bound collision_bound)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma wp_composition_fri_challenge_set_hit_bound_via_supported_partial_union_or_collision:
  fixes C H :: prob
  assumes future: "composition_fri_future_fresh s"
    and union_bound:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots.
        nnreal
          (card
            (composition_fri_supported_root_partial_union_bad_sets s bad_sets
              fr f_fri_roots f_final as dg composition_fri_roots)) /
          nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (composition_fri_challenge_set_hit s bad_sets) s \<le>
      C + H"
proof -
  have partial_bound:
    "wp_event verify_monad
      (composition_fri_root_list_set_hit s
        (composition_fri_supported_root_partial_union_bad_sets s bad_sets))
      s \<le> C"
    by (rule wp_verify_monad_composition_fri_root_list_set_bound[OF future])
      (use composition_fri_supported_root_partial_union_bad_sets_subset
        union_bound in simp_all)
  show ?thesis
    by (rule
        wp_composition_fri_challenge_set_hit_bound_via_partial_union_or_collision
        [OF partial_bound collision_bound])
qed

lemma wp_composition_fri_challenge_set_hit_bound_if_supported_partial_root_candidate_unique_or_collision:
  fixes H :: prob
  assumes future: "composition_fri_future_fresh s"
    and unique:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots.
        \<exists>composition_table.
          composition_fri_supported_root_partial_composition_table_candidates
            s fr f_fri_roots f_final as dg composition_fri_roots \<subseteq>
            {composition_table}"
    and bounded: "composition_fri_bad_challenge_sets_bounded bad_sets"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (composition_fri_challenge_set_hit s bad_sets) s \<le>
      composition_fri_error + H"
proof -
  have union_bound:
    "\<And>fr f_fri_roots f_final as dg composition_fri_roots.
      nnreal
        (card
          (composition_fri_supported_root_partial_union_bad_sets s bad_sets
            fr f_fri_roots f_final as dg composition_fri_roots)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
      composition_fri_error"
  proof -
    fix fr f_fri_roots f_final as dg composition_fri_roots
    show "nnreal
        (card
          (composition_fri_supported_root_partial_union_bad_sets s bad_sets
            fr f_fri_roots f_final as dg composition_fri_roots)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
      composition_fri_error"
      by (rule
          composition_fri_supported_root_partial_union_bad_sets_fraction_bound_if_unique_candidate
          [OF unique])
        (use bounded in
          \<open>auto simp: composition_fri_bad_challenge_sets_bounded_def\<close>)
  qed
  show ?thesis
    by (rule
        wp_composition_fri_challenge_set_hit_bound_via_supported_partial_union_or_collision
        [OF future union_bound collision_bound])
qed

definition trace_fri_bad_with_tables
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_bad_with_tables s out \<longleftrightarrow>
      accepted_with_fri_tables s out \<and> trace_fri_bad s out"

definition composition_fri_bad_with_tables
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_fri_bad_with_tables s out \<longleftrightarrow>
      accepted_with_fri_tables s out \<and> composition_fri_bad s out"

definition trace_fri_bad_with_partial_openings
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_bad_with_partial_openings s out \<longleftrightarrow>
      trace_fri_bad s out \<and>
      (\<exists>fr query_idxs trace_openings.
        accepted_with_partial_trace_openings s out fr query_idxs
          trace_openings)"

definition composition_fri_bad_with_partial_openings
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_fri_bad_with_partial_openings s out \<longleftrightarrow>
      composition_fri_bad s out \<and>
      (\<exists>fr query_idxs trace_openings.
        accepted_with_partial_trace_openings s out fr query_idxs
          trace_openings)"

end

end
