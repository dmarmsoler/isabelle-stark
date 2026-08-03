(*  Title:      Stark/Staged_Security_Experiment_Targets.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Targets
  imports Staged_Security_Experiment_Budgets
begin

text \<open>Bad-value target events and checked-prefix probability bounds.\<close>

context soundness
begin

definition staged_query_prefix_bad_index_error
  :: "staged_budgets \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> prob"
  where
    "staged_query_prefix_bad_index_error budgets B i =
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_query_search_queries budgets i)"

definition fri_vector_position_values :: "'f list set \<Rightarrow> nat \<Rightarrow> 'f set"
  where
    "fri_vector_position_values B i =
      {b. \<exists>bs \<in> B. i < length bs \<and> bs ! i = b}"

lemma fri_vector_position_valueI:
  assumes "bs \<in> B"
    and "i < length bs"
  shows "bs ! i \<in> fri_vector_position_values B i"
  using assms unfolding fri_vector_position_values_def by blast

lemma fri_vector_member_imp_position_value:
  assumes subset: "B \<subseteq> fri_challenge_space n"
    and member: "bs \<in> B"
    and i_bound: "i < n"
  shows "bs ! i \<in> fri_vector_position_values B i"
proof -
  have "length bs = n"
    using subset member unfolding fri_challenge_space_def by auto
  then have "i < length bs"
    using i_bound by simp
  then show ?thesis
    by (rule fri_vector_position_valueI[OF member])
qed

lemma fri_vector_member_imp_first_position_value:
  assumes subset: "B \<subseteq> fri_challenge_space n"
    and member: "bs \<in> B"
    and nonempty: "0 < n"
  shows "bs ! 0 \<in> fri_vector_position_values B 0"
  by (rule fri_vector_member_imp_position_value[OF subset member])
    (use nonempty in simp)

lemma fri_vector_extend_member_imp_position_value:
  assumes member: "bs @ [b] \<in> B"
    and length: "length bs = i"
  shows "b \<in> fri_vector_position_values B i"
  using assms unfolding fri_vector_position_values_def by force

lemma fri_vector_position_values_card_le:
  assumes subset: "B \<subseteq> fri_challenge_space n"
    and i_bound: "i < n"
  shows "card (fri_vector_position_values B i) \<le> card B"
proof -
  have finite_B: "finite B"
    by (rule finite_subset[OF subset finite_fri_challenge_space])
  have values_eq:
    "fri_vector_position_values B i = (\<lambda>bs. bs ! i) ` B"
    using subset i_bound
    unfolding fri_vector_position_values_def fri_challenge_space_def
    by auto
  show ?thesis
    unfolding values_eq by (rule card_image_le[OF finite_B])
qed

lemma fri_vector_member_coordinate_cover:
  assumes subset: "B \<subseteq> fri_challenge_space n"
    and member: "bs \<in> B"
    and nonempty: "0 < n"
  shows "\<exists>i < n. bs ! i \<in> fri_vector_position_values B i"
proof -
  have "bs ! 0 \<in> fri_vector_position_values B 0"
    by (rule fri_vector_member_imp_first_position_value
        [OF subset member nonempty])
  then show ?thesis
    using nonempty by blast
qed

definition trace_fri_challenge_values_absent
  :: "'f set \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "trace_fri_challenge_values_absent B s \<longleftrightarrow>
      (\<forall>i x y.
        fmlookup (HashMap s) (TraceFriChallenge i x) = Some y \<longrightarrow>
        y \<notin> B)"

definition composition_fri_challenge_values_absent
  :: "'f set \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "composition_fri_challenge_values_absent B s \<longleftrightarrow>
      (\<forall>i x y.
        fmlookup (HashMap s) (CompositionFriChallenge i x) = Some y \<longrightarrow>
        y \<notin> B)"

definition alpha_challenge_values_absent
  :: "'f set \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "alpha_challenge_values_absent B s \<longleftrightarrow>
      (\<forall>i x y.
        fmlookup (HashMap s) (AlphaChallenge i x) = Some y \<longrightarrow>
        y \<notin> B)"

definition query_index_raw_preimage_absent
  :: "nat set \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "query_index_raw_preimage_absent B s \<longleftrightarrow>
      (\<forall>i x raw.
        fmlookup (HashMap s) (QueryIndexChallenge i x) = Some raw \<longrightarrow>
        raw \<notin> query_index_raw_preimage B)"

lemma staged_query_prefix_bad_index_error_eq:
  "staged_query_prefix_bad_index_error budgets B i =
    hash_target_budget_value (query_index_raw_preimage B)
      (staged_query_search_queries budgets i)"
  unfolding staged_query_prefix_bad_index_error_def
    staged_phase_target_error_def by simp

lemma trace_fri_challenge_values_absent_empty[simp]:
  "trace_fri_challenge_values_absent B
    (s\<lparr>HashMap := fmempty\<rparr>)"
  unfolding trace_fri_challenge_values_absent_def by simp

lemma composition_fri_challenge_values_absent_empty[simp]:
  "composition_fri_challenge_values_absent B
    (s\<lparr>HashMap := fmempty\<rparr>)"
  unfolding composition_fri_challenge_values_absent_def by simp

lemma alpha_challenge_values_absent_empty[simp]:
  "alpha_challenge_values_absent B
    (s\<lparr>HashMap := fmempty\<rparr>)"
  unfolding alpha_challenge_values_absent_def by simp

lemma staged_query_prefix_bad_index_target_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (staged_query_challenge_prefix_program A i)
      (hash_new_output_hit_event (query_index_raw_preimage B) s) s \<le>
      staged_query_prefix_bad_index_error budgets B i"
  unfolding staged_query_prefix_bad_index_error_def
  by (rule staged_query_prefix_target_hit_bound[OF wf controlled i_bound])

lemma query_index_raw_preimage_absent_empty[simp]:
  "query_index_raw_preimage_absent B
    (s\<lparr>HashMap := fmempty\<rparr>)"
  unfolding query_index_raw_preimage_absent_def by simp

lemma staged_trace_fri_prefix_receive_bad_value_imp_new_output_hit:
  assumes controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < length (trace_fri_budgets budgets)"
    and absent: "trace_fri_challenge_values_absent B s"
    and out:
      "Some (b, t) \<in>
        set_dist
          (execute
            (staged_trace_fri_challenge_prefix_program A i \<bind>
              (\<lambda>_. receive_trace_fri_challenge)) s)"
    and bad: "b \<in> B"
  shows "hash_new_output_hit_event B s (Some (b, t))"
proof -
  obtain prefix_out u where prefix:
      "Some (prefix_out, u) \<in>
        set_dist
          (execute (staged_trace_fri_challenge_prefix_program A i) s)"
    and recv:
      "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge u)"
    using out by (auto elim!: set_dist_bindE)
  have prefix_ext: "s \<le> u"
    using hash_target_program_staged_trace_fri_challenge_prefix_program
        [OF controlled i_bound, of B] prefix
    unfolding hash_target_program_def hash_extension_preserving_def
    by blast
  have recv_out:
    "u \<le> t \<and>
     fmlookup (HashMap t)
       (TraceFriChallenge (PTraceFriCounter u) (PState u)) = Some b"
    using receive_trace_fri_challenge_outcome[OF recv] by blast
  show ?thesis
  proof (cases
      "fmlookup (HashMap s)
        (TraceFriChallenge (PTraceFriCounter u) (PState u))")
    case None
    then have "hash_map_new_output_hit B s t"
      unfolding hash_map_new_output_hit_def
      using recv_out bad by blast
    then show ?thesis
      unfolding hash_new_output_hit_event_def by simp
  next
    case (Some old_b)
    have old_lookup_t:
      "fmlookup (HashMap t)
        (TraceFriChallenge (PTraceFriCounter u) (PState u)) = Some old_b"
      by (rule hash_extension_lookup[OF Some])
        (rule hash_ext_trans[OF prefix_ext conjunct1[OF recv_out]])
    then have old_eq: "old_b = b"
      using recv_out by simp
    have "old_b \<notin> B"
      using absent Some
      unfolding trace_fri_challenge_values_absent_def by blast
    then show ?thesis
      using old_eq bad by simp
  qed
qed

lemma staged_trace_fri_prefix_receive_bad_value_bound:
  assumes controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < length (trace_fri_budgets budgets)"
    and absent: "trace_fri_challenge_values_absent B s"
  shows
    "wp_event
      (staged_trace_fri_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_trace_fri_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (b, _) \<Rightarrow> b \<in> B) s \<le>
      staged_phase_target_error B
        (Suc (staged_trace_fri_search_queries budgets i))"
proof -
  let ?m =
    "staged_trace_fri_challenge_prefix_program A i \<bind>
      (\<lambda>_. receive_trace_fri_challenge)"
  let ?bad =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (b, _) \<Rightarrow> b \<in> B"
  let ?hit = "hash_new_output_hit_event B s"
  have bad_imp_hit:
    "wp_event ?m ?bad s \<le> wp_event ?m ?hit s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?m s)"
      and bad: "?bad out"
    show "?hit out"
    proof (cases out)
      case None
      then show ?thesis using bad by simp
    next
      case (Some bt)
      then obtain b t where out_eq: "out = Some (b, t)"
        by (cases bt) simp
      have out':
        "Some (b, t) \<in> set_dist (execute ?m s)"
        using support out_eq by simp
      have b_in: "b \<in> B"
        using bad out_eq by simp
      show ?thesis
        unfolding out_eq
        by (rule staged_trace_fri_prefix_receive_bad_value_imp_new_output_hit
            [OF controlled i_bound absent out' b_in])
    qed
  qed
  have prefix_target:
    "hash_target_program B
      (staged_trace_fri_search_queries budgets i)
      (staged_trace_fri_challenge_prefix_program A i)"
    by (rule hash_target_program_staged_trace_fri_challenge_prefix_program
        [OF controlled i_bound])
  have target:
    "hash_target_program B
      (staged_trace_fri_search_queries budgets i + 1) ?m"
    by (rule hash_target_program_bind[OF prefix_target])
      (rule hash_target_program_receive_trace_fri_challenge)
  have hit_bound:
    "wp_event ?m ?hit s \<le>
      staged_phase_target_error B
        (staged_trace_fri_search_queries budgets i + 1)"
    using target unfolding hash_target_program_def hash_target_budget_def
      staged_phase_target_error_def by blast
  show ?thesis
    using order_trans[OF bad_imp_hit hit_bound] by simp
qed

lemma staged_composition_fri_prefix_receive_bad_value_imp_new_output_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < ceil_log (maxDegree + 1)"
    and absent: "composition_fri_challenge_values_absent B s"
    and out:
      "Some (b, t) \<in>
        set_dist
          (execute
            (staged_composition_fri_challenge_prefix_program A i \<bind>
              (\<lambda>_. receive_composition_fri_challenge)) s)"
    and bad: "b \<in> B"
  shows "hash_new_output_hit_event B s (Some (b, t))"
proof -
  obtain prefix_out u where prefix:
      "Some (prefix_out, u) \<in>
        set_dist
          (execute (staged_composition_fri_challenge_prefix_program A i) s)"
    and recv:
      "Some (b, t) \<in>
        set_dist (execute receive_composition_fri_challenge u)"
    using out by (auto elim!: set_dist_bindE)
  have prefix_ext: "s \<le> u"
    using hash_target_program_staged_composition_fri_challenge_prefix_program
        [OF wf controlled i_bound, of B] prefix
    unfolding hash_target_program_def hash_extension_preserving_def
    by blast
  have recv_out:
    "u \<le> t \<and>
     fmlookup (HashMap t)
       (CompositionFriChallenge (PCompositionFriCounter u) (PState u)) =
       Some b"
    using receive_composition_fri_challenge_outcome[OF recv] by blast
  show ?thesis
  proof (cases
      "fmlookup (HashMap s)
        (CompositionFriChallenge (PCompositionFriCounter u) (PState u))")
    case None
    then have "hash_map_new_output_hit B s t"
      unfolding hash_map_new_output_hit_def
      using recv_out bad by blast
    then show ?thesis
      unfolding hash_new_output_hit_event_def by simp
  next
    case (Some old_b)
    have old_lookup_t:
      "fmlookup (HashMap t)
        (CompositionFriChallenge (PCompositionFriCounter u) (PState u)) =
        Some old_b"
      by (rule hash_extension_lookup[OF Some])
        (rule hash_ext_trans[OF prefix_ext conjunct1[OF recv_out]])
    then have old_eq: "old_b = b"
      using recv_out by simp
    have "old_b \<notin> B"
      using absent Some
      unfolding composition_fri_challenge_values_absent_def by blast
    then show ?thesis
      using old_eq bad by simp
  qed
qed

lemma staged_composition_fri_prefix_receive_bad_value_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < ceil_log (maxDegree + 1)"
    and absent: "composition_fri_challenge_values_absent B s"
  shows
    "wp_event
      (staged_composition_fri_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_composition_fri_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (b, _) \<Rightarrow> b \<in> B) s \<le>
      staged_phase_target_error B
        (Suc (staged_composition_fri_search_queries budgets i))"
proof -
  let ?m =
    "staged_composition_fri_challenge_prefix_program A i \<bind>
      (\<lambda>_. receive_composition_fri_challenge)"
  let ?bad =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (b, _) \<Rightarrow> b \<in> B"
  let ?hit = "hash_new_output_hit_event B s"
  have bad_imp_hit:
    "wp_event ?m ?bad s \<le> wp_event ?m ?hit s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?m s)"
      and bad: "?bad out"
    show "?hit out"
    proof (cases out)
      case None
      then show ?thesis using bad by simp
    next
      case (Some bt)
      then obtain b t where out_eq: "out = Some (b, t)"
        by (cases bt) simp
      have out':
        "Some (b, t) \<in> set_dist (execute ?m s)"
        using support out_eq by simp
      have b_in: "b \<in> B"
        using bad out_eq by simp
      show ?thesis
        unfolding out_eq
        by (rule
            staged_composition_fri_prefix_receive_bad_value_imp_new_output_hit
            [OF wf controlled i_bound absent out' b_in])
    qed
  qed
  have prefix_target:
    "hash_target_program B
      (staged_composition_fri_search_queries budgets i)
      (staged_composition_fri_challenge_prefix_program A i)"
    by (rule
        hash_target_program_staged_composition_fri_challenge_prefix_program
        [OF wf controlled i_bound])
  have target:
    "hash_target_program B
      (staged_composition_fri_search_queries budgets i + 1) ?m"
    by (rule hash_target_program_bind[OF prefix_target])
      (rule hash_target_program_receive_composition_fri_challenge)
  have hit_bound:
    "wp_event ?m ?hit s \<le>
      staged_phase_target_error B
        (staged_composition_fri_search_queries budgets i + 1)"
    using target unfolding hash_target_program_def hash_target_budget_def
      staged_phase_target_error_def by blast
  show ?thesis
    using order_trans[OF bad_imp_hit hit_bound] by simp
qed

lemma staged_query_prefix_receive_bad_index_imp_new_output_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
    and absent: "query_index_raw_preimage_absent B s"
    and out:
      "Some (raw, t) \<in>
        set_dist
          (execute
            (staged_query_challenge_prefix_program A i \<bind>
              (\<lambda>_. receive_query_index_challenge)) s)"
    and bad: "index (to_nat raw) \<in> B"
  shows
    "hash_new_output_hit_event (query_index_raw_preimage B) s
      (Some (raw, t))"
proof -
  obtain prefix_out u where prefix:
      "Some (prefix_out, u) \<in>
        set_dist (execute (staged_query_challenge_prefix_program A i) s)"
    and recv:
      "Some (raw, t) \<in>
        set_dist (execute receive_query_index_challenge u)"
    using out by (auto elim!: set_dist_bindE)
  have prefix_ext:
    "s \<le> u"
    using hash_target_program_staged_query_challenge_prefix_program
        [OF wf controlled i_bound, of "query_index_raw_preimage B"]
      prefix
    unfolding hash_target_program_def hash_extension_preserving_def
    by blast
  have recv_out:
    "u \<le> t \<and>
     fmlookup (HashMap t)
       (QueryIndexChallenge (PQueryCounter u) (PState u)) = Some raw"
    using receive_query_index_challenge_outcome[OF recv] by blast
  have raw_in: "raw \<in> query_index_raw_preimage B"
    using bad unfolding query_index_raw_preimage_def by simp
  show ?thesis
  proof (cases
      "fmlookup (HashMap s)
        (QueryIndexChallenge (PQueryCounter u) (PState u))")
    case None
    then have "hash_map_new_output_hit (query_index_raw_preimage B) s t"
      unfolding hash_map_new_output_hit_def
      using recv_out raw_in by blast
    then show ?thesis
      unfolding hash_new_output_hit_event_def by simp
  next
    case (Some old_raw)
    have old_lookup_t:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter u) (PState u)) =
        Some old_raw"
      by (rule hash_extension_lookup[OF Some])
        (rule hash_ext_trans[OF prefix_ext conjunct1[OF recv_out]])
    then have old_eq: "old_raw = raw"
      using recv_out by simp
    have "old_raw \<notin> query_index_raw_preimage B"
      using absent Some
      unfolding query_index_raw_preimage_absent_def by blast
    then show ?thesis
      using old_eq raw_in by simp
  qed
qed

lemma staged_query_prefix_receive_bad_index_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
    and absent: "query_index_raw_preimage_absent B s"
  shows
    "wp_event
      (staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_query_index_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B) s \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (Suc (staged_query_search_queries budgets i))"
proof -
  let ?m =
    "staged_query_challenge_prefix_program A i \<bind>
      (\<lambda>_. receive_query_index_challenge)"
  let ?B = "query_index_raw_preimage B"
  let ?bad =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B"
  let ?hit = "hash_new_output_hit_event ?B s"
  have bad_imp_hit:
    "wp_event ?m ?bad s \<le> wp_event ?m ?hit s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?m s)"
      and bad: "?bad out"
    show "?hit out"
    proof (cases out)
      case None
      then show ?thesis using bad by simp
    next
      case (Some rt)
      then obtain raw t where out_eq: "out = Some (raw, t)"
        by (cases rt) simp
      have out':
        "Some (raw, t) \<in> set_dist (execute ?m s)"
        using support out_eq by simp
      have bad_raw: "index (to_nat raw) \<in> B"
        using bad out_eq by simp
      show ?thesis
        unfolding out_eq
        by (rule staged_query_prefix_receive_bad_index_imp_new_output_hit
            [OF wf controlled i_bound absent out' bad_raw])
    qed
  qed
  have prefix_target:
    "hash_target_program ?B
      (staged_query_search_queries budgets i)
      (staged_query_challenge_prefix_program A i)"
    by (rule hash_target_program_staged_query_challenge_prefix_program
        [OF wf controlled i_bound])
  have target:
    "hash_target_program ?B
      (staged_query_search_queries budgets i + 1) ?m"
    by (rule hash_target_program_bind[OF prefix_target])
      (rule hash_target_program_receive_query_index_challenge)
  have hit_bound:
    "wp_event ?m ?hit s \<le>
      staged_phase_target_error ?B
        (staged_query_search_queries budgets i + 1)"
    using target unfolding hash_target_program_def hash_target_budget_def
      staged_phase_target_error_def by blast
  show ?thesis
    using order_trans[OF bad_imp_hit hit_bound] by simp
qed

lemma receive_alpha_challenge_bad_value_imp_new_output_hit:
  assumes absent: "alpha_challenge_values_absent B s"
    and out:
      "Some (a, t) \<in> set_dist (execute receive_alpha_challenge s)"
    and bad: "a \<in> B"
  shows "hash_new_output_hit_event B s (Some (a, t))"
proof -
  have recv_out:
    "s \<le> t \<and>
     fmlookup (HashMap t)
       (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using receive_alpha_challenge_outcome[OF out] by blast
  show ?thesis
  proof (cases
      "fmlookup (HashMap s)
        (AlphaChallenge (PAlphaCounter s) (PState s))")
    case None
    then have "hash_map_new_output_hit B s t"
      unfolding hash_map_new_output_hit_def
      using recv_out bad by blast
    then show ?thesis
      unfolding hash_new_output_hit_event_def by simp
  next
    case (Some old_a)
    have old_lookup_t:
      "fmlookup (HashMap t)
        (AlphaChallenge (PAlphaCounter s) (PState s)) = Some old_a"
      by (rule hash_extension_lookup[OF Some conjunct1[OF recv_out]])
    then have old_eq: "old_a = a"
      using recv_out by simp
    have "old_a \<notin> B"
      using absent Some
      unfolding alpha_challenge_values_absent_def by blast
    then show ?thesis
      using old_eq bad by simp
  qed
qed

lemma receive_alpha_challenge_bad_value_bound:
  assumes absent: "alpha_challenge_values_absent B s"
  shows
    "wp_event receive_alpha_challenge
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (a, _) \<Rightarrow> a \<in> B) s \<le>
      staged_phase_target_error B 1"
proof -
  let ?bad =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (a, _) \<Rightarrow> a \<in> B"
  let ?hit = "hash_new_output_hit_event B s"
  have bad_imp_hit:
    "wp_event receive_alpha_challenge ?bad s \<le>
      wp_event receive_alpha_challenge ?hit s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute receive_alpha_challenge s)"
      and bad: "?bad out"
    show "?hit out"
    proof (cases out)
      case None
      then show ?thesis using bad by simp
    next
      case (Some pair)
      obtain a t where pair_eq: "pair = (a, t)"
        by (cases pair)
      have out_eq: "out = Some (a, t)"
        using Some pair_eq by simp
      have out':
        "Some (a, t) \<in> set_dist (execute receive_alpha_challenge s)"
        using support out_eq by simp
      have a_in: "a \<in> B"
        using bad out_eq by simp
      show ?thesis
        unfolding out_eq
        by (rule receive_alpha_challenge_bad_value_imp_new_output_hit
            [OF absent out' a_in])
    qed
  qed
  have target:
    "hash_target_program B 1 receive_alpha_challenge"
    by (rule hash_target_program_receive_alpha_challenge)
  have hit_bound:
    "wp_event receive_alpha_challenge ?hit s \<le>
      staged_phase_target_error B 1"
    using target unfolding hash_target_program_def hash_target_budget_def
      staged_phase_target_error_def by blast
  show ?thesis
    using order_trans[OF bad_imp_hit hit_bound] .
qed

lemma staged_alpha_prefix_receive_bad_value_imp_new_output_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> length spec"
    and absent: "alpha_challenge_values_absent B s"
    and out:
      "Some (a, t) \<in>
        set_dist
          (execute
            (staged_alpha_challenge_prefix_program A i \<bind>
              (\<lambda>_. receive_alpha_challenge)) s)"
    and bad: "a \<in> B"
  shows "hash_new_output_hit_event B s (Some (a, t))"
proof -
  obtain prefix_out u where prefix:
      "Some (prefix_out, u) \<in>
        set_dist (execute (staged_alpha_challenge_prefix_program A i) s)"
    and recv:
      "Some (a, t) \<in> set_dist (execute receive_alpha_challenge u)"
    using out by (auto elim!: set_dist_bindE)
  have prefix_ext:
    "s \<le> u"
    using hash_target_program_staged_alpha_challenge_prefix_program
        [OF wf controlled i_bound, of B] prefix
    unfolding hash_target_program_def hash_extension_preserving_def
    by blast
  have recv_out:
    "u \<le> t \<and>
     fmlookup (HashMap t)
       (AlphaChallenge (PAlphaCounter u) (PState u)) = Some a"
    using receive_alpha_challenge_outcome[OF recv] by blast
  show ?thesis
  proof (cases
      "fmlookup (HashMap s)
        (AlphaChallenge (PAlphaCounter u) (PState u))")
    case None
    then have "hash_map_new_output_hit B s t"
      unfolding hash_map_new_output_hit_def
      using recv_out bad by blast
    then show ?thesis
      unfolding hash_new_output_hit_event_def by simp
  next
    case (Some old_a)
    have old_lookup_t:
      "fmlookup (HashMap t)
        (AlphaChallenge (PAlphaCounter u) (PState u)) = Some old_a"
      by (rule hash_extension_lookup[OF Some])
        (rule hash_ext_trans[OF prefix_ext conjunct1[OF recv_out]])
    then have old_eq: "old_a = a"
      using recv_out by simp
    have "old_a \<notin> B"
      using absent Some
      unfolding alpha_challenge_values_absent_def by blast
    then show ?thesis
      using old_eq bad by simp
  qed
qed

lemma staged_alpha_prefix_receive_bad_value_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> length spec"
    and absent: "alpha_challenge_values_absent B s"
  shows
    "wp_event
      (staged_alpha_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_alpha_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (a, _) \<Rightarrow> a \<in> B) s \<le>
      staged_phase_target_error B
        (Suc (staged_alpha_search_queries budgets i))"
proof -
  let ?m =
    "staged_alpha_challenge_prefix_program A i \<bind>
      (\<lambda>_. receive_alpha_challenge)"
  let ?bad =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (a, _) \<Rightarrow> a \<in> B"
  let ?hit = "hash_new_output_hit_event B s"
  have bad_imp_hit:
    "wp_event ?m ?bad s \<le> wp_event ?m ?hit s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?m s)"
      and bad: "?bad out"
    show "?hit out"
    proof (cases out)
      case None
      then show ?thesis using bad by simp
    next
      case (Some pair)
      obtain a t where pair_eq: "pair = (a, t)"
        by (cases pair)
      have out_eq: "out = Some (a, t)"
        using Some pair_eq by simp
      have out':
        "Some (a, t) \<in> set_dist (execute ?m s)"
        using support out_eq by simp
      have a_in: "a \<in> B"
        using bad out_eq by simp
      show ?thesis
        unfolding out_eq
        by (rule staged_alpha_prefix_receive_bad_value_imp_new_output_hit
            [OF wf controlled i_bound absent out' a_in])
    qed
  qed
  have prefix_target:
    "hash_target_program B (staged_alpha_search_queries budgets i)
      (staged_alpha_challenge_prefix_program A i)"
    by (rule hash_target_program_staged_alpha_challenge_prefix_program
        [OF wf controlled i_bound])
  have target:
    "hash_target_program B
      (staged_alpha_search_queries budgets i + 1) ?m"
    by (rule hash_target_program_bind[OF prefix_target])
      (rule hash_target_program_receive_alpha_challenge)
  have hit_bound:
    "wp_event ?m ?hit s \<le>
      staged_phase_target_error B
        (staged_alpha_search_queries budgets i + 1)"
    using target unfolding hash_target_program_def hash_target_budget_def
      staged_phase_target_error_def by blast
  show ?thesis
    using order_trans[OF bad_imp_hit hit_bound] by simp
qed

lemma hash_range_budget_staged_transcript_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (staged_transcript_program A)"
proof -
  let ?trace_root = "trace_root_budget budgets"
  let ?trace_fri =
    "sum_list (trace_fri_budgets budgets) + ceil_log clength"
  let ?trace_final = "trace_final_budget budgets"
  let ?alpha = "length spec"
  let ?degree = "degree_budget budgets"
  let ?composition_fri =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  let ?composition_final = "composition_final_budget budgets"
  let ?query =
    "sum_list (query_opening_budgets budgets) + rounds"
  have trace_root_range:
    "hash_range_budget ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have trace_fri_range:
    "hash_range_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_range_budget
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          ceil_log clength)
        (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_range_budget_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_final_range:
    "\<And>bs. hash_range_budget ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have alpha_range:
    "hash_range_budget ?alpha (staged_alpha_program (length spec))"
    by (rule hash_range_budget_staged_alpha_program)
  have degree_range:
    "\<And>as. hash_range_budget ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have composition_fri_range:
    "\<And>dg. hash_range_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_range_budget_guarded_staged_composition_fri_program
        [OF wf controlled])
  have composition_final_range:
    "\<And>dg bs. hash_range_budget ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have query_range:
    "hash_range_budget ?query (staged_query_program A 0 rounds)"
  proof -
    have len:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_range_budget
        (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) +
          rounds)
        (staged_query_program A 0 rounds)"
      by (rule hash_range_budget_staged_query_program[OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have query_tail:
    "\<And>F. hash_range_budget (?query + 0)
      (staged_query_program A 0 rounds \<bind>
        (\<lambda>query_chunks. return (F query_chunks)))"
    by (rule hash_range_budget_bind)
      (rule query_range, rule hash_range_budget_return)
  have after_composition_final_record:
    "\<And>composition_final F. hash_range_budget (0 + (?query + 0))
      (record_staged_message composition_final \<bind>
        (\<lambda>_. staged_query_program A 0 rounds \<bind>
          (\<lambda>query_chunks. return (F query_chunks))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message, rule query_tail)
  have after_composition_final:
    "\<And>dg bs F. hash_range_budget
      (?composition_final + (0 + (?query + 0)))
      (composition_final_stage A dg bs \<bind>
        (\<lambda>composition_final.
          record_staged_message composition_final \<bind>
            (\<lambda>_. staged_query_program A 0 rounds \<bind>
              (\<lambda>query_chunks.
                return (F composition_final query_chunks)))))"
    by (rule hash_range_budget_bind)
      (rule composition_final_range, rule after_composition_final_record)
  have after_composition_fri:
    "\<And>dg F. hash_range_budget
      (?composition_fri +
        (?composition_final + (0 + (?query + 0))))
      ((assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])) \<bind>
        (\<lambda>(composition_roots, composition_bs).
          composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 rounds \<bind>
                  (\<lambda>query_chunks.
                    return
                      (F composition_roots composition_bs composition_final
                        query_chunks))))))"
  proof (rule hash_range_budget_bind)
    fix dg F
    show "hash_range_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri_range)
    fix dg F x
    show "hash_range_budget
      (?composition_final + (0 + (?query + 0)))
      (case x of (composition_roots, composition_bs) \<Rightarrow>
        composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
    proof (cases x)
      case (Pair composition_roots composition_bs)
      have "hash_range_budget
        (?composition_final + (0 + (?query + 0)))
        (composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
        by (rule after_composition_final)
      then show ?thesis
        unfolding Pair by simp
    qed
  qed
  have after_degree_record:
    "\<And>dg F. hash_range_budget
      (0 +
        (?composition_fri +
          (?composition_final + (0 + (?query + 0)))))
      (record_staged_message dg \<bind>
        (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [])) \<bind>
          (\<lambda>(composition_roots, composition_bs).
            composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                  (\<lambda>_. staged_query_program A 0 rounds \<bind>
                    (\<lambda>query_chunks.
                      return
                        (F composition_roots composition_bs composition_final
                          query_chunks)))))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message, rule after_composition_fri)
  have after_degree:
    "\<And>as F. hash_range_budget
      (?degree +
        (0 +
          (?composition_fri +
            (?composition_final + (0 + (?query + 0))))))
      (degree_stage A as \<bind>
        (\<lambda>dg. record_staged_message dg \<bind>
          (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
            ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])) \<bind>
            (\<lambda>(composition_roots, composition_bs).
              composition_final_stage A dg composition_bs \<bind>
                (\<lambda>composition_final.
                  record_staged_message composition_final \<bind>
                    (\<lambda>_. staged_query_program A 0 rounds \<bind>
                      (\<lambda>query_chunks.
                        return
                          (F dg composition_roots composition_bs
                            composition_final query_chunks))))))))"
    by (rule hash_range_budget_bind)
      (rule degree_range, rule after_degree_record)
  have after_alpha:
    "\<And>F. hash_range_budget
      (?alpha +
        (?degree +
          (0 +
            (?composition_fri +
              (?composition_final + (0 + (?query + 0)))))))
      (staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
              ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                (ceil_log (to_nat dg + 1)) [])) \<bind>
              (\<lambda>(composition_roots, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                      (\<lambda>_. staged_query_program A 0 rounds \<bind>
                        (\<lambda>query_chunks.
                          return
                            (F as dg composition_roots composition_bs
                              composition_final query_chunks)))))))))"
    by (rule hash_range_budget_bind)
      (rule alpha_range, rule after_degree)
  have after_trace_final_record:
    "\<And>trace_final F. hash_range_budget
      (0 +
        (?alpha +
          (?degree +
            (0 +
              (?composition_fri +
                (?composition_final + (0 + (?query + 0))))))))
      (record_staged_message trace_final \<bind>
        (\<lambda>_. staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  (ceil_log (to_nat dg + 1)) [])) \<bind>
                (\<lambda>(composition_roots, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                        (\<lambda>_. staged_query_program A 0 rounds \<bind>
                          (\<lambda>query_chunks.
                            return
                              (F as dg composition_roots composition_bs
                                composition_final query_chunks))))))))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message, rule after_alpha)
  have after_trace_final:
    "\<And>trace_bs F. hash_range_budget
      (?trace_final +
        (0 +
          (?alpha +
            (?degree +
              (0 +
                (?composition_fri +
                  (?composition_final + (0 + (?query + 0)))))))))
      (trace_final_stage A trace_bs \<bind>
        (\<lambda>trace_final. record_staged_message trace_final \<bind>
          (\<lambda>_. staged_alpha_program (length spec) \<bind>
            (\<lambda>as. degree_stage A as \<bind>
              (\<lambda>dg. record_staged_message dg \<bind>
                (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                  ceil_log (maxDegree + 1)) \<bind>
                  (\<lambda>_. staged_composition_fri_program A dg 0
                    (ceil_log (to_nat dg + 1)) [])) \<bind>
                  (\<lambda>(composition_roots, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        record_staged_message composition_final \<bind>
                          (\<lambda>_. staged_query_program A 0 rounds \<bind>
                            (\<lambda>query_chunks.
                              return
                                (F trace_final as dg composition_roots
                                  composition_bs composition_final
                                  query_chunks)))))))))))"
    by (rule hash_range_budget_bind)
      (rule trace_final_range, rule after_trace_final_record)
  have after_trace_fri:
    "\<And>F. hash_range_budget
      (?trace_fri +
        (?trace_final +
          (0 +
            (?alpha +
              (?degree +
                (0 +
                  (?composition_fri +
                    (?composition_final + (0 + (?query + 0))))))))))
      (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final. record_staged_message trace_final \<bind>
              (\<lambda>_. staged_alpha_program (length spec) \<bind>
                (\<lambda>as. degree_stage A as \<bind>
                  (\<lambda>dg. record_staged_message dg \<bind>
                    (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                      ceil_log (maxDegree + 1)) \<bind>
                      (\<lambda>_. staged_composition_fri_program A dg 0
                        (ceil_log (to_nat dg + 1)) [])) \<bind>
                      (\<lambda>(composition_roots, composition_bs).
                        composition_final_stage A dg composition_bs \<bind>
                          (\<lambda>composition_final.
                            record_staged_message composition_final \<bind>
                              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                                (\<lambda>query_chunks.
                                  return
                                    (F trace_roots trace_bs trace_final as dg
                                      composition_roots composition_bs
                                      composition_final query_chunks))))))))))))"
  proof (rule hash_range_budget_bind)
    fix F
    show "hash_range_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_range)
    fix F x
    show "hash_range_budget
      (?trace_final +
        (0 +
          (?alpha +
            (?degree +
              (0 +
                (?composition_fri +
                  (?composition_final + (0 + (?query + 0)))))))))
      (case x of (trace_roots, trace_bs) \<Rightarrow>
        trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. record_staged_message trace_final \<bind>
            (\<lambda>_. staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
    proof (cases x)
      case (Pair trace_roots trace_bs)
      have "hash_range_budget
        (?trace_final +
          (0 +
            (?alpha +
              (?degree +
                (0 +
                  (?composition_fri +
                    (?composition_final + (0 + (?query + 0)))))))))
        (trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. record_staged_message trace_final \<bind>
            (\<lambda>_. staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
        by (rule after_trace_final)
      then show ?thesis
        unfolding Pair by simp
    qed
  qed
  have after_trace_root_record:
    "\<And>fr F. hash_range_budget
      (0 +
        (?trace_fri +
          (?trace_final +
            (0 +
              (?alpha +
                (?degree +
                  (0 +
                    (?composition_fri +
                      (?composition_final + (0 + (?query + 0)))))))))))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final. record_staged_message trace_final \<bind>
                (\<lambda>_. staged_alpha_program (length spec) \<bind>
                  (\<lambda>as. degree_stage A as \<bind>
                    (\<lambda>dg. record_staged_message dg \<bind>
                      (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                        ceil_log (maxDegree + 1)) \<bind>
                        (\<lambda>_. staged_composition_fri_program A dg 0
                          (ceil_log (to_nat dg + 1)) [])) \<bind>
                        (\<lambda>(composition_roots, composition_bs).
                          composition_final_stage A dg composition_bs \<bind>
                            (\<lambda>composition_final.
                              record_staged_message composition_final \<bind>
                                (\<lambda>_. staged_query_program A 0 rounds \<bind>
                                  (\<lambda>query_chunks.
                                    return
                                      (F trace_roots trace_bs trace_final as dg
                                        composition_roots composition_bs
                                        composition_final query_chunks)))))))))))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message, rule after_trace_fri)
  have whole:
    "hash_range_budget
      (?trace_root +
        (0 +
          (?trace_fri +
            (?trace_final +
              (0 +
                (?alpha +
                  (?degree +
                    (0 +
                      (?composition_fri +
                        (?composition_final + (0 + (?query + 0))))))))))))
      (staged_transcript_program A)"
    unfolding staged_transcript_program_def Let_def
  proof (rule hash_range_budget_bind)
    show "hash_range_budget ?trace_root (trace_root_stage A)"
      by (rule trace_root_range)
    fix fr
    show "hash_range_budget
      (0 +
        (?trace_fri +
          (?trace_final +
            (0 +
              (?alpha +
                (?degree +
                  (0 +
                    (?composition_fri +
                      (?composition_final + (0 + (?query + 0)))))))))))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final.
                record_staged_message trace_final \<bind>
                  (\<lambda>_. staged_alpha_program (length spec) \<bind>
                    (\<lambda>as. degree_stage A as \<bind>
                      (\<lambda>dg. record_staged_message dg \<bind>
                        (\<lambda>_. assert (ceil_log (to_nat dg + 1) \<le>
                          ceil_log (maxDegree + 1)) \<bind>
                          (\<lambda>_. staged_composition_fri_program A dg 0
                            (ceil_log (to_nat dg + 1)) [] \<bind>
                            (\<lambda>(composition_roots, composition_bs).
                              composition_final_stage A dg composition_bs \<bind>
                                (\<lambda>composition_final.
                                  record_staged_message
                                    composition_final \<bind>
                                    (\<lambda>_. staged_query_program A 0
                                      rounds \<bind>
                                      (\<lambda>query_chunks.
                                        return
                                          \<lparr>staged_trace_root = fr,
                                           staged_trace_fri_roots =
                                            trace_roots,
                                           staged_trace_fri_challenges =
                                            trace_bs,
                                           staged_trace_final =
                                            trace_final,
                                           staged_alphas = as,
                                           staged_degree = dg,
                                           staged_composition_fri_roots =
                                            composition_roots,
                                           staged_composition_fri_challenges =
                                            composition_bs,
                                           staged_composition_final =
                                            composition_final,
                                           staged_query_chunks =
                                            query_chunks\<rparr>)))))))))))))"
      using after_trace_root_record
        [of fr
          "\<lambda>trace_roots trace_bs trace_final as dg composition_roots
              composition_bs composition_final query_chunks.
            \<lparr>staged_trace_root = fr,
             staged_trace_fri_roots = trace_roots,
             staged_trace_fri_challenges = trace_bs,
             staged_trace_final = trace_final,
             staged_alphas = as,
             staged_degree = dg,
             staged_composition_fri_roots = composition_roots,
             staged_composition_fri_challenges = composition_bs,
             staged_composition_final = composition_final,
             staged_query_chunks = query_chunks\<rparr>"]
      by (simp add: sm_bind_assoc)
  qed
  have budget_eq:
    "?trace_root +
        (0 +
          (?trace_fri +
            (?trace_final +
              (0 +
                (?alpha +
                  (?degree +
                    (0 +
                      (?composition_fri +
                        (?composition_final + (0 + (?query + 0))))))))))) =
      staged_attacker_query_budget budgets + staged_challenge_query_budget"
    unfolding staged_attacker_query_budget_def
      staged_challenge_query_budget_def
    by (simp add: add.assoc add.commute add.left_commute)
  show ?thesis
    using whole unfolding budget_eq .
qed

lemma hash_range_budget_staged_semantic_adversary:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (staged_semantic_adversary A)"
proof -
  have "hash_range_budget
    ((staged_attacker_query_budget budgets + staged_challenge_query_budget) +
      0)
    (staged_semantic_adversary A)"
    unfolding staged_semantic_adversary_def
  proof (rule hash_range_budget_bind
      [where n="staged_attacker_query_budget budgets +
        staged_challenge_query_budget" and n'=0])
    show "hash_range_budget
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (staged_transcript_program A)"
      by (rule hash_range_budget_staged_transcript_program[OF wf controlled])
    show "\<And>x. hash_range_budget 0 (return (staged_proof_transcript x))"
      by (rule hash_range_budget_return)
  qed
  then show ?thesis by simp
qed

lemma hash_collision_budget_staged_transcript_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_collision_budget
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (staged_transcript_program A)"
proof -
  let ?trace_root = "trace_root_budget budgets"
  let ?trace_fri =
    "sum_list (trace_fri_budgets budgets) + ceil_log clength"
  let ?trace_final = "trace_final_budget budgets"
  let ?alpha = "length spec"
  let ?degree = "degree_budget budgets"
  let ?composition_fri =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  let ?composition_final = "composition_final_budget budgets"
  let ?query =
    "sum_list (query_opening_budgets budgets) + rounds"
  have trace_root_range:
    "hash_range_budget ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have trace_root_coll:
    "hash_collision_budget ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have trace_fri_range:
    "hash_range_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_range_budget
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          ceil_log clength)
        (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_range_budget_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_fri_coll:
    "hash_collision_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_collision_budget
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          ceil_log clength)
        (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_collision_budget_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_final_range:
    "\<And>bs. hash_range_budget ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have trace_final_coll:
    "\<And>bs. hash_collision_budget ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have alpha_range:
    "hash_range_budget ?alpha (staged_alpha_program (length spec))"
    by (rule hash_range_budget_staged_alpha_program)
  have alpha_coll:
    "hash_collision_budget ?alpha (staged_alpha_program (length spec))"
    by (rule hash_collision_budget_staged_alpha_program)
  have degree_range:
    "\<And>as. hash_range_budget ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have degree_coll:
    "\<And>as. hash_collision_budget ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have composition_fri_range:
    "\<And>dg. hash_range_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_range_budget_guarded_staged_composition_fri_program
        [OF wf controlled])
  have composition_fri_coll:
    "\<And>dg. hash_collision_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_collision_budget_guarded_staged_composition_fri_program
        [OF wf controlled])
  have composition_final_range:
    "\<And>dg bs. hash_range_budget ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have composition_final_coll:
    "\<And>dg bs. hash_collision_budget ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_collision)
  have query_range:
    "hash_range_budget ?query (staged_query_program A 0 rounds)"
  proof -
    have len:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_range_budget
        (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) +
          rounds)
        (staged_query_program A 0 rounds)"
      by (rule hash_range_budget_staged_query_program[OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have query_coll:
    "hash_collision_budget ?query (staged_query_program A 0 rounds)"
  proof -
    have len:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_collision_budget
        (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) +
          rounds)
        (staged_query_program A 0 rounds)"
      by (rule hash_collision_budget_staged_query_program[OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have query_tail_range:
    "\<And>F. hash_range_budget (?query + 0)
      (staged_query_program A 0 rounds \<bind>
        (\<lambda>query_chunks. return (F query_chunks)))"
    by (rule hash_range_budget_bind)
      (rule query_range, rule hash_range_budget_return)
  have query_tail_coll:
    "\<And>F. hash_collision_budget (?query + 0)
      (staged_query_program A 0 rounds \<bind>
        (\<lambda>query_chunks. return (F query_chunks)))"
    by (rule hash_collision_budget_bind)
      (rule query_range, rule query_coll, rule hash_range_budget_return,
        rule hash_collision_budget_return)
  have after_composition_final_record_range:
    "\<And>composition_final F. hash_range_budget (0 + (?query + 0))
      (record_staged_message composition_final \<bind>
        (\<lambda>_. staged_query_program A 0 rounds \<bind>
          (\<lambda>query_chunks. return (F query_chunks))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message, rule query_tail_range)
  have after_composition_final_record_coll:
    "\<And>composition_final F. hash_collision_budget (0 + (?query + 0))
      (record_staged_message composition_final \<bind>
        (\<lambda>_. staged_query_program A 0 rounds \<bind>
          (\<lambda>query_chunks. return (F query_chunks))))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule hash_collision_budget_record_staged_message,
        rule query_tail_range, rule query_tail_coll)
  have after_composition_final_range:
    "\<And>dg bs F. hash_range_budget
      (?composition_final + (0 + (?query + 0)))
      (composition_final_stage A dg bs \<bind>
        (\<lambda>composition_final.
          record_staged_message composition_final \<bind>
            (\<lambda>_. staged_query_program A 0 rounds \<bind>
              (\<lambda>query_chunks.
                return (F composition_final query_chunks)))))"
    by (rule hash_range_budget_bind)
      (rule composition_final_range,
        rule after_composition_final_record_range)
  have after_composition_final_coll:
    "\<And>dg bs F. hash_collision_budget
      (?composition_final + (0 + (?query + 0)))
      (composition_final_stage A dg bs \<bind>
        (\<lambda>composition_final.
          record_staged_message composition_final \<bind>
            (\<lambda>_. staged_query_program A 0 rounds \<bind>
              (\<lambda>query_chunks.
                return (F composition_final query_chunks)))))"
    by (rule hash_collision_budget_bind)
      (rule composition_final_range, rule composition_final_coll,
        rule after_composition_final_record_range,
        rule after_composition_final_record_coll)
  have after_composition_fri_range:
    "\<And>dg F. hash_range_budget
      (?composition_fri +
        (?composition_final + (0 + (?query + 0))))
      ((assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])) \<bind>
        (\<lambda>(composition_roots, composition_bs).
          composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 rounds \<bind>
                  (\<lambda>query_chunks.
                    return
                      (F composition_roots composition_bs composition_final
                        query_chunks))))))"
  proof (rule hash_range_budget_bind)
    fix dg F
    show "hash_range_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri_range)
    fix dg F x
    show "hash_range_budget
      (?composition_final + (0 + (?query + 0)))
      (case x of (composition_roots, composition_bs) \<Rightarrow>
        composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
    proof (cases x)
      case (Pair composition_roots composition_bs)
      have "hash_range_budget
        (?composition_final + (0 + (?query + 0)))
        (composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
        by (rule after_composition_final_range)
      then show ?thesis
        unfolding Pair by simp
    qed
  qed
  have after_composition_fri_coll:
    "\<And>dg F. hash_collision_budget
      (?composition_fri +
        (?composition_final + (0 + (?query + 0))))
      ((assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])) \<bind>
        (\<lambda>(composition_roots, composition_bs).
          composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 rounds \<bind>
                  (\<lambda>query_chunks.
                    return
                      (F composition_roots composition_bs composition_final
                        query_chunks))))))"
  proof (rule hash_collision_budget_bind)
    fix dg F
    show "hash_range_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri_range)
    fix dg F
    show "hash_collision_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri_coll)
    fix dg F x
    show "hash_range_budget
      (?composition_final + (0 + (?query + 0)))
      (case x of (composition_roots, composition_bs) \<Rightarrow>
        composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
    proof (cases x)
      case (Pair composition_roots composition_bs)
      have "hash_range_budget
        (?composition_final + (0 + (?query + 0)))
        (composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
        by (rule after_composition_final_range)
      then show ?thesis
        unfolding Pair by simp
    qed
    fix dg F x
    show "hash_collision_budget
      (?composition_final + (0 + (?query + 0)))
      (case x of (composition_roots, composition_bs) \<Rightarrow>
        composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
    proof (cases x)
      case (Pair composition_roots composition_bs)
      have "hash_collision_budget
        (?composition_final + (0 + (?query + 0)))
        (composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
        by (rule after_composition_final_coll)
      then show ?thesis
        unfolding Pair by simp
    qed
  qed
  have after_degree_record_range:
    "\<And>dg F. hash_range_budget
      (0 +
        (?composition_fri +
          (?composition_final + (0 + (?query + 0)))))
      (record_staged_message dg \<bind>
        (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [])) \<bind>
          (\<lambda>(composition_roots, composition_bs).
            composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                  (\<lambda>_. staged_query_program A 0 rounds \<bind>
                    (\<lambda>query_chunks.
                      return
                        (F composition_roots composition_bs composition_final
                          query_chunks)))))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule after_composition_fri_range)
  have after_degree_record_coll:
    "\<And>dg F. hash_collision_budget
      (0 +
        (?composition_fri +
          (?composition_final + (0 + (?query + 0)))))
      (record_staged_message dg \<bind>
        (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [])) \<bind>
          (\<lambda>(composition_roots, composition_bs).
            composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                  (\<lambda>_. staged_query_program A 0 rounds \<bind>
                    (\<lambda>query_chunks.
                      return
                        (F composition_roots composition_bs composition_final
                          query_chunks)))))))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule hash_collision_budget_record_staged_message,
        rule after_composition_fri_range, rule after_composition_fri_coll)
  have after_degree_range:
    "\<And>as F. hash_range_budget
      (?degree +
        (0 +
          (?composition_fri +
            (?composition_final + (0 + (?query + 0))))))
      (degree_stage A as \<bind>
        (\<lambda>dg. record_staged_message dg \<bind>
          (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
            ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])) \<bind>
            (\<lambda>(composition_roots, composition_bs).
              composition_final_stage A dg composition_bs \<bind>
                (\<lambda>composition_final.
                  record_staged_message composition_final \<bind>
                    (\<lambda>_. staged_query_program A 0 rounds \<bind>
                      (\<lambda>query_chunks.
                        return
                          (F dg composition_roots composition_bs
                            composition_final query_chunks))))))))"
    by (rule hash_range_budget_bind)
      (rule degree_range, rule after_degree_record_range)
  have after_degree_coll:
    "\<And>as F. hash_collision_budget
      (?degree +
        (0 +
          (?composition_fri +
            (?composition_final + (0 + (?query + 0))))))
      (degree_stage A as \<bind>
        (\<lambda>dg. record_staged_message dg \<bind>
          (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
            ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])) \<bind>
            (\<lambda>(composition_roots, composition_bs).
              composition_final_stage A dg composition_bs \<bind>
                (\<lambda>composition_final.
                  record_staged_message composition_final \<bind>
                    (\<lambda>_. staged_query_program A 0 rounds \<bind>
                      (\<lambda>query_chunks.
                        return
                          (F dg composition_roots composition_bs
                            composition_final query_chunks))))))))"
    by (rule hash_collision_budget_bind)
      (rule degree_range, rule degree_coll, rule after_degree_record_range,
        rule after_degree_record_coll)
  have after_alpha_range:
    "\<And>F. hash_range_budget
      (?alpha +
        (?degree +
          (0 +
            (?composition_fri +
              (?composition_final + (0 + (?query + 0)))))))
      (staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
              ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                (ceil_log (to_nat dg + 1)) [])) \<bind>
              (\<lambda>(composition_roots, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                      (\<lambda>_. staged_query_program A 0 rounds \<bind>
                        (\<lambda>query_chunks.
                          return
                            (F as dg composition_roots composition_bs
                              composition_final query_chunks)))))))))"
    by (rule hash_range_budget_bind)
      (rule alpha_range, rule after_degree_range)
  have after_alpha_coll:
    "\<And>F. hash_collision_budget
      (?alpha +
        (?degree +
          (0 +
            (?composition_fri +
              (?composition_final + (0 + (?query + 0)))))))
      (staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
              ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                (ceil_log (to_nat dg + 1)) [])) \<bind>
              (\<lambda>(composition_roots, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                      (\<lambda>_. staged_query_program A 0 rounds \<bind>
                        (\<lambda>query_chunks.
                          return
                            (F as dg composition_roots composition_bs
                              composition_final query_chunks)))))))))"
    by (rule hash_collision_budget_bind)
      (rule alpha_range, rule alpha_coll, rule after_degree_range,
        rule after_degree_coll)
  have after_trace_final_record_range:
    "\<And>trace_final F. hash_range_budget
      (0 +
        (?alpha +
          (?degree +
            (0 +
              (?composition_fri +
                (?composition_final + (0 + (?query + 0))))))))
      (record_staged_message trace_final \<bind>
        (\<lambda>_. staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  (ceil_log (to_nat dg + 1)) [])) \<bind>
                (\<lambda>(composition_roots, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                        (\<lambda>_. staged_query_program A 0 rounds \<bind>
                          (\<lambda>query_chunks.
                            return
                              (F as dg composition_roots composition_bs
                                composition_final query_chunks))))))))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule after_alpha_range)
  have after_trace_final_record_coll:
    "\<And>trace_final F. hash_collision_budget
      (0 +
        (?alpha +
          (?degree +
            (0 +
              (?composition_fri +
                (?composition_final + (0 + (?query + 0))))))))
      (record_staged_message trace_final \<bind>
        (\<lambda>_. staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  (ceil_log (to_nat dg + 1)) [])) \<bind>
                (\<lambda>(composition_roots, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                        (\<lambda>_. staged_query_program A 0 rounds \<bind>
                          (\<lambda>query_chunks.
                            return
                              (F as dg composition_roots composition_bs
                                composition_final query_chunks))))))))))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule hash_collision_budget_record_staged_message,
        rule after_alpha_range, rule after_alpha_coll)
  have after_trace_final_range:
    "\<And>trace_bs F. hash_range_budget
      (?trace_final +
        (0 +
          (?alpha +
            (?degree +
              (0 +
                (?composition_fri +
                  (?composition_final + (0 + (?query + 0)))))))))
      (trace_final_stage A trace_bs \<bind>
        (\<lambda>trace_final. record_staged_message trace_final \<bind>
          (\<lambda>_. staged_alpha_program (length spec) \<bind>
            (\<lambda>as. degree_stage A as \<bind>
              (\<lambda>dg. record_staged_message dg \<bind>
                (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                  ceil_log (maxDegree + 1)) \<bind>
                  (\<lambda>_. staged_composition_fri_program A dg 0
                    (ceil_log (to_nat dg + 1)) [])) \<bind>
                  (\<lambda>(composition_roots, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        record_staged_message composition_final \<bind>
                          (\<lambda>_. staged_query_program A 0 rounds \<bind>
                            (\<lambda>query_chunks.
                              return
                                (F trace_final as dg composition_roots
                                  composition_bs composition_final
                                  query_chunks)))))))))))"
    by (rule hash_range_budget_bind)
      (rule trace_final_range, rule after_trace_final_record_range)
  have after_trace_final_coll:
    "\<And>trace_bs F. hash_collision_budget
      (?trace_final +
        (0 +
          (?alpha +
            (?degree +
              (0 +
                (?composition_fri +
                  (?composition_final + (0 + (?query + 0)))))))))
      (trace_final_stage A trace_bs \<bind>
        (\<lambda>trace_final. record_staged_message trace_final \<bind>
          (\<lambda>_. staged_alpha_program (length spec) \<bind>
            (\<lambda>as. degree_stage A as \<bind>
              (\<lambda>dg. record_staged_message dg \<bind>
                (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                  ceil_log (maxDegree + 1)) \<bind>
                  (\<lambda>_. staged_composition_fri_program A dg 0
                    (ceil_log (to_nat dg + 1)) [])) \<bind>
                  (\<lambda>(composition_roots, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        record_staged_message composition_final \<bind>
                          (\<lambda>_. staged_query_program A 0 rounds \<bind>
                            (\<lambda>query_chunks.
                              return
                                (F trace_final as dg composition_roots
                                  composition_bs composition_final
                                  query_chunks)))))))))))"
    by (rule hash_collision_budget_bind)
      (rule trace_final_range, rule trace_final_coll,
        rule after_trace_final_record_range,
        rule after_trace_final_record_coll)
  have after_trace_fri_range:
    "\<And>F. hash_range_budget
      (?trace_fri +
        (?trace_final +
          (0 +
            (?alpha +
              (?degree +
                (0 +
                  (?composition_fri +
                    (?composition_final + (0 + (?query + 0))))))))))
      (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final. record_staged_message trace_final \<bind>
              (\<lambda>_. staged_alpha_program (length spec) \<bind>
                (\<lambda>as. degree_stage A as \<bind>
                  (\<lambda>dg. record_staged_message dg \<bind>
                    (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                      ceil_log (maxDegree + 1)) \<bind>
                      (\<lambda>_. staged_composition_fri_program A dg 0
                        (ceil_log (to_nat dg + 1)) [])) \<bind>
                      (\<lambda>(composition_roots, composition_bs).
                        composition_final_stage A dg composition_bs \<bind>
                          (\<lambda>composition_final.
                            record_staged_message composition_final \<bind>
                              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                                (\<lambda>query_chunks.
                                  return
                                    (F trace_roots trace_bs trace_final as dg
                                      composition_roots composition_bs
                                      composition_final query_chunks))))))))))))"
  proof (rule hash_range_budget_bind)
    fix F
    show "hash_range_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_range)
    fix F x
    show "hash_range_budget
      (?trace_final +
        (0 +
          (?alpha +
            (?degree +
              (0 +
                (?composition_fri +
                  (?composition_final + (0 + (?query + 0)))))))))
      (case x of (trace_roots, trace_bs) \<Rightarrow>
        trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. record_staged_message trace_final \<bind>
            (\<lambda>_. staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
    proof (cases x)
      case (Pair trace_roots trace_bs)
      have "hash_range_budget
        (?trace_final +
          (0 +
            (?alpha +
              (?degree +
                (0 +
                  (?composition_fri +
                    (?composition_final + (0 + (?query + 0)))))))))
        (trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. record_staged_message trace_final \<bind>
            (\<lambda>_. staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
        by (rule after_trace_final_range)
      then show ?thesis
        unfolding Pair by simp
    qed
  qed
  have after_trace_fri_coll:
    "\<And>F. hash_collision_budget
      (?trace_fri +
        (?trace_final +
          (0 +
            (?alpha +
              (?degree +
                (0 +
                  (?composition_fri +
                    (?composition_final + (0 + (?query + 0))))))))))
      (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final. record_staged_message trace_final \<bind>
              (\<lambda>_. staged_alpha_program (length spec) \<bind>
                (\<lambda>as. degree_stage A as \<bind>
                  (\<lambda>dg. record_staged_message dg \<bind>
                    (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                      ceil_log (maxDegree + 1)) \<bind>
                      (\<lambda>_. staged_composition_fri_program A dg 0
                        (ceil_log (to_nat dg + 1)) [])) \<bind>
                      (\<lambda>(composition_roots, composition_bs).
                        composition_final_stage A dg composition_bs \<bind>
                          (\<lambda>composition_final.
                            record_staged_message composition_final \<bind>
                              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                                (\<lambda>query_chunks.
                                  return
                                    (F trace_roots trace_bs trace_final as dg
                                      composition_roots composition_bs
                                      composition_final query_chunks))))))))))))"
  proof (rule hash_collision_budget_bind)
    fix F
    show "hash_range_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_range)
    fix F
    show "hash_collision_budget ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_coll)
    fix F x
    show "hash_range_budget
      (?trace_final +
        (0 +
          (?alpha +
            (?degree +
              (0 +
                (?composition_fri +
                  (?composition_final + (0 + (?query + 0)))))))))
      (case x of (trace_roots, trace_bs) \<Rightarrow>
        trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. record_staged_message trace_final \<bind>
            (\<lambda>_. staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
    proof (cases x)
      case (Pair trace_roots trace_bs)
      have "hash_range_budget
        (?trace_final +
          (0 +
            (?alpha +
              (?degree +
                (0 +
                  (?composition_fri +
                    (?composition_final + (0 + (?query + 0)))))))))
        (trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. record_staged_message trace_final \<bind>
            (\<lambda>_. staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
        by (rule after_trace_final_range)
      then show ?thesis
        unfolding Pair by simp
    qed
    fix F x
    show "hash_collision_budget
      (?trace_final +
        (0 +
          (?alpha +
            (?degree +
              (0 +
                (?composition_fri +
                  (?composition_final + (0 + (?query + 0)))))))))
      (case x of (trace_roots, trace_bs) \<Rightarrow>
        trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. record_staged_message trace_final \<bind>
            (\<lambda>_. staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
    proof (cases x)
      case (Pair trace_roots trace_bs)
      have "hash_collision_budget
        (?trace_final +
          (0 +
            (?alpha +
              (?degree +
                (0 +
                  (?composition_fri +
                    (?composition_final + (0 + (?query + 0)))))))))
        (trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. record_staged_message trace_final \<bind>
            (\<lambda>_. staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
        by (rule after_trace_final_coll)
      then show ?thesis
        unfolding Pair by simp
    qed
  qed
  have after_trace_root_record_range:
    "\<And>fr F. hash_range_budget
      (0 +
        (?trace_fri +
          (?trace_final +
            (0 +
              (?alpha +
                (?degree +
                  (0 +
                    (?composition_fri +
                      (?composition_final + (0 + (?query + 0)))))))))))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final. record_staged_message trace_final \<bind>
                (\<lambda>_. staged_alpha_program (length spec) \<bind>
                  (\<lambda>as. degree_stage A as \<bind>
                    (\<lambda>dg. record_staged_message dg \<bind>
                      (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                        ceil_log (maxDegree + 1)) \<bind>
                        (\<lambda>_. staged_composition_fri_program A dg 0
                          (ceil_log (to_nat dg + 1)) [])) \<bind>
                        (\<lambda>(composition_roots, composition_bs).
                          composition_final_stage A dg composition_bs \<bind>
                            (\<lambda>composition_final.
                              record_staged_message composition_final \<bind>
                                (\<lambda>_. staged_query_program A 0 rounds \<bind>
                                  (\<lambda>query_chunks.
                                    return
                                      (F trace_roots trace_bs trace_final as dg
                                        composition_roots composition_bs
                                        composition_final query_chunks)))))))))))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule after_trace_fri_range)
  have after_trace_root_record_coll:
    "\<And>fr F. hash_collision_budget
      (0 +
        (?trace_fri +
          (?trace_final +
            (0 +
              (?alpha +
                (?degree +
                  (0 +
                    (?composition_fri +
                      (?composition_final + (0 + (?query + 0)))))))))))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final. record_staged_message trace_final \<bind>
                (\<lambda>_. staged_alpha_program (length spec) \<bind>
                  (\<lambda>as. degree_stage A as \<bind>
                    (\<lambda>dg. record_staged_message dg \<bind>
                      (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                        ceil_log (maxDegree + 1)) \<bind>
                        (\<lambda>_. staged_composition_fri_program A dg 0
                          (ceil_log (to_nat dg + 1)) [])) \<bind>
                        (\<lambda>(composition_roots, composition_bs).
                          composition_final_stage A dg composition_bs \<bind>
                            (\<lambda>composition_final.
                              record_staged_message composition_final \<bind>
                                (\<lambda>_. staged_query_program A 0 rounds \<bind>
                                  (\<lambda>query_chunks.
                                    return
                                      (F trace_roots trace_bs trace_final as dg
                                        composition_roots composition_bs
                                        composition_final query_chunks)))))))))))))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_record_staged_message,
        rule hash_collision_budget_record_staged_message,
        rule after_trace_fri_range, rule after_trace_fri_coll)
  have whole:
    "hash_collision_budget
      (?trace_root +
        (0 +
          (?trace_fri +
            (?trace_final +
              (0 +
                (?alpha +
                  (?degree +
                    (0 +
                      (?composition_fri +
                        (?composition_final + (0 + (?query + 0))))))))))))
      (staged_transcript_program A)"
    unfolding staged_transcript_program_def Let_def
  proof (rule hash_collision_budget_bind)
    show "hash_range_budget ?trace_root (trace_root_stage A)"
      by (rule trace_root_range)
    show "hash_collision_budget ?trace_root (trace_root_stage A)"
      by (rule trace_root_coll)
    fix fr
    show "hash_range_budget
      (0 +
        (?trace_fri +
          (?trace_final +
            (0 +
              (?alpha +
                (?degree +
                  (0 +
                    (?composition_fri +
                      (?composition_final + (0 + (?query + 0)))))))))))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final.
                record_staged_message trace_final \<bind>
                  (\<lambda>_. staged_alpha_program (length spec) \<bind>
                    (\<lambda>as. degree_stage A as \<bind>
                      (\<lambda>dg. record_staged_message dg \<bind>
                        (\<lambda>_. assert (ceil_log (to_nat dg + 1) \<le>
                          ceil_log (maxDegree + 1)) \<bind>
                          (\<lambda>_. staged_composition_fri_program A dg 0
                            (ceil_log (to_nat dg + 1)) [] \<bind>
                            (\<lambda>(composition_roots, composition_bs).
                              composition_final_stage A dg composition_bs \<bind>
                                (\<lambda>composition_final.
                                  record_staged_message
                                    composition_final \<bind>
                                    (\<lambda>_. staged_query_program A 0
                                      rounds \<bind>
                                      (\<lambda>query_chunks.
                                        return
                                          \<lparr>staged_trace_root = fr,
                                           staged_trace_fri_roots =
                                            trace_roots,
                                           staged_trace_fri_challenges =
                                            trace_bs,
                                           staged_trace_final =
                                            trace_final,
                                           staged_alphas = as,
                                           staged_degree = dg,
                                           staged_composition_fri_roots =
                                            composition_roots,
                                           staged_composition_fri_challenges =
                                            composition_bs,
                                           staged_composition_final =
                                            composition_final,
                                           staged_query_chunks =
                                            query_chunks\<rparr>)))))))))))))"
      using after_trace_root_record_range
        [of fr
          "\<lambda>trace_roots trace_bs trace_final as dg composition_roots
              composition_bs composition_final query_chunks.
            \<lparr>staged_trace_root = fr,
             staged_trace_fri_roots = trace_roots,
             staged_trace_fri_challenges = trace_bs,
             staged_trace_final = trace_final,
             staged_alphas = as,
             staged_degree = dg,
             staged_composition_fri_roots = composition_roots,
             staged_composition_fri_challenges = composition_bs,
             staged_composition_final = composition_final,
             staged_query_chunks = query_chunks\<rparr>"]
      by (simp add: sm_bind_assoc)
    fix fr
    show "hash_collision_budget
      (0 +
        (?trace_fri +
          (?trace_final +
            (0 +
              (?alpha +
                (?degree +
                  (0 +
                    (?composition_fri +
                      (?composition_final + (0 + (?query + 0)))))))))))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final.
                record_staged_message trace_final \<bind>
                  (\<lambda>_. staged_alpha_program (length spec) \<bind>
                    (\<lambda>as. degree_stage A as \<bind>
                      (\<lambda>dg. record_staged_message dg \<bind>
                        (\<lambda>_. assert (ceil_log (to_nat dg + 1) \<le>
                          ceil_log (maxDegree + 1)) \<bind>
                          (\<lambda>_. staged_composition_fri_program A dg 0
                            (ceil_log (to_nat dg + 1)) [] \<bind>
                            (\<lambda>(composition_roots, composition_bs).
                              composition_final_stage A dg composition_bs \<bind>
                                (\<lambda>composition_final.
                                  record_staged_message
                                    composition_final \<bind>
                                    (\<lambda>_. staged_query_program A 0
                                      rounds \<bind>
                                      (\<lambda>query_chunks.
                                        return
                                          \<lparr>staged_trace_root = fr,
                                           staged_trace_fri_roots =
                                            trace_roots,
                                           staged_trace_fri_challenges =
                                            trace_bs,
                                           staged_trace_final =
                                            trace_final,
                                           staged_alphas = as,
                                           staged_degree = dg,
                                           staged_composition_fri_roots =
                                            composition_roots,
                                           staged_composition_fri_challenges =
                                            composition_bs,
                                           staged_composition_final =
                                            composition_final,
                                           staged_query_chunks =
                                            query_chunks\<rparr>)))))))))))))"
      using after_trace_root_record_coll
        [of fr
          "\<lambda>trace_roots trace_bs trace_final as dg composition_roots
              composition_bs composition_final query_chunks.
            \<lparr>staged_trace_root = fr,
             staged_trace_fri_roots = trace_roots,
             staged_trace_fri_challenges = trace_bs,
             staged_trace_final = trace_final,
             staged_alphas = as,
             staged_degree = dg,
             staged_composition_fri_roots = composition_roots,
             staged_composition_fri_challenges = composition_bs,
             staged_composition_final = composition_final,
             staged_query_chunks = query_chunks\<rparr>"]
      by (simp add: sm_bind_assoc)
  qed
  have budget_eq:
    "?trace_root +
        (0 +
          (?trace_fri +
            (?trace_final +
              (0 +
                (?alpha +
                  (?degree +
                    (0 +
                      (?composition_fri +
                        (?composition_final + (0 + (?query + 0))))))))))) =
      staged_attacker_query_budget budgets + staged_challenge_query_budget"
    unfolding staged_attacker_query_budget_def
      staged_challenge_query_budget_def
    by (simp add: add.assoc add.commute add.left_commute)
  show ?thesis
    using whole unfolding budget_eq .
qed

lemma hash_collision_budget_staged_semantic_adversary:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_collision_budget
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (staged_semantic_adversary A)"
proof -
  have "hash_collision_budget
    ((staged_attacker_query_budget budgets + staged_challenge_query_budget) +
      0)
    (staged_semantic_adversary A)"
    unfolding staged_semantic_adversary_def
  proof (rule hash_collision_budget_bind
      [where n="staged_attacker_query_budget budgets +
        staged_challenge_query_budget" and n'=0])
    show "hash_range_budget
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (staged_transcript_program A)"
      by (rule hash_range_budget_staged_transcript_program[OF wf controlled])
    show "hash_collision_budget
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (staged_transcript_program A)"
      by (rule hash_collision_budget_staged_transcript_program
          [OF wf controlled])
    show "\<And>x. hash_range_budget 0 (return (staged_proof_transcript x))"
      by (rule hash_range_budget_return)
    show "\<And>x. hash_collision_budget 0
      (return (staged_proof_transcript x))"
      by (rule hash_collision_budget_return)
  qed
  then show ?thesis by simp
qed

lemma hash_target_program_staged_transcript_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (staged_transcript_program A)"
proof -
  let ?trace_root = "trace_root_budget budgets"
  let ?trace_fri =
    "sum_list (trace_fri_budgets budgets) + ceil_log clength"
  let ?trace_final = "trace_final_budget budgets"
  let ?alpha = "length spec"
  let ?degree = "degree_budget budgets"
  let ?composition_fri =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  let ?composition_final = "composition_final_budget budgets"
  let ?query =
    "sum_list (query_opening_budgets budgets) + rounds"
  have trace_root_target:
    "hash_target_program B ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have trace_fri_target:
    "hash_target_program B ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_target_program B
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          ceil_log clength)
        (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_target_program_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_final_target:
    "\<And>bs. hash_target_program B ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have alpha_target:
    "hash_target_program B ?alpha (staged_alpha_program (length spec))"
    by (rule hash_target_program_staged_alpha_program)
  have degree_target:
    "\<And>as. hash_target_program B ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have composition_fri_target:
    "\<And>dg. hash_target_program B ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_target_program_guarded_staged_composition_fri_program
        [OF wf controlled])
  have composition_final_target:
    "\<And>dg bs. hash_target_program B ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have query_target:
    "hash_target_program B ?query (staged_query_program A 0 rounds)"
  proof -
    have len:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_target_program B
        (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) +
          rounds)
        (staged_query_program A 0 rounds)"
      by (rule hash_target_program_staged_query_program[OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have query_tail:
    "\<And>F. hash_target_program B (?query + 0)
      (staged_query_program A 0 rounds \<bind>
        (\<lambda>query_chunks. return (F query_chunks)))"
    by (rule hash_target_program_bind)
      (rule query_target, rule hash_target_program_return)
  have after_composition_final_record:
    "\<And>composition_final F. hash_target_program B (0 + (?query + 0))
      (record_staged_message composition_final \<bind>
        (\<lambda>_. staged_query_program A 0 rounds \<bind>
          (\<lambda>query_chunks. return (F query_chunks))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message, rule query_tail)
  have after_composition_final:
    "\<And>dg bs F. hash_target_program B
      (?composition_final + (0 + (?query + 0)))
      (composition_final_stage A dg bs \<bind>
        (\<lambda>composition_final.
          record_staged_message composition_final \<bind>
            (\<lambda>_. staged_query_program A 0 rounds \<bind>
              (\<lambda>query_chunks.
                return (F composition_final query_chunks)))))"
    by (rule hash_target_program_bind)
      (rule composition_final_target, rule after_composition_final_record)
  have after_composition_fri:
    "\<And>dg F. hash_target_program B
      (?composition_fri +
        (?composition_final + (0 + (?query + 0))))
      ((assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])) \<bind>
        (\<lambda>(composition_roots, composition_bs).
          composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. staged_query_program A 0 rounds \<bind>
                  (\<lambda>query_chunks.
                    return
                      (F composition_roots composition_bs composition_final
                        query_chunks))))))"
  proof (rule hash_target_program_bind)
    fix dg F
    show "hash_target_program B ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri_target)
    fix dg F x
    show "hash_target_program B
      (?composition_final + (0 + (?query + 0)))
      (case x of (composition_roots, composition_bs) \<Rightarrow>
        composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
    proof (cases x)
      case (Pair composition_roots composition_bs)
      have "hash_target_program B
        (?composition_final + (0 + (?query + 0)))
        (composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
        by (rule after_composition_final)
      then show ?thesis
        unfolding Pair by simp
    qed
  qed
  have after_degree_record:
    "\<And>dg F. hash_target_program B
      (0 +
        (?composition_fri +
          (?composition_final + (0 + (?query + 0)))))
      (record_staged_message dg \<bind>
        (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [])) \<bind>
          (\<lambda>(composition_roots, composition_bs).
            composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                  (\<lambda>_. staged_query_program A 0 rounds \<bind>
                    (\<lambda>query_chunks.
                      return
                        (F composition_roots composition_bs composition_final
                          query_chunks)))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message, rule after_composition_fri)
  have after_degree:
    "\<And>as F. hash_target_program B
      (?degree +
        (0 +
          (?composition_fri +
            (?composition_final + (0 + (?query + 0))))))
      (degree_stage A as \<bind>
        (\<lambda>dg. record_staged_message dg \<bind>
          (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
            ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])) \<bind>
            (\<lambda>(composition_roots, composition_bs).
              composition_final_stage A dg composition_bs \<bind>
                (\<lambda>composition_final.
                  record_staged_message composition_final \<bind>
                    (\<lambda>_. staged_query_program A 0 rounds \<bind>
                      (\<lambda>query_chunks.
                        return
                          (F dg composition_roots composition_bs
                            composition_final query_chunks))))))))"
    by (rule hash_target_program_bind)
      (rule degree_target, rule after_degree_record)
  have after_alpha:
    "\<And>F. hash_target_program B
      (?alpha +
        (?degree +
          (0 +
            (?composition_fri +
              (?composition_final + (0 + (?query + 0)))))))
      (staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
              ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                (ceil_log (to_nat dg + 1)) [])) \<bind>
              (\<lambda>(composition_roots, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                      (\<lambda>_. staged_query_program A 0 rounds \<bind>
                        (\<lambda>query_chunks.
                          return
                            (F as dg composition_roots composition_bs
                              composition_final query_chunks)))))))))"
    by (rule hash_target_program_bind)
      (rule alpha_target, rule after_degree)
  have after_trace_final_record:
    "\<And>trace_final F. hash_target_program B
      (0 +
        (?alpha +
          (?degree +
            (0 +
              (?composition_fri +
                (?composition_final + (0 + (?query + 0))))))))
      (record_staged_message trace_final \<bind>
        (\<lambda>_. staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  (ceil_log (to_nat dg + 1)) [])) \<bind>
                (\<lambda>(composition_roots, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                        (\<lambda>_. staged_query_program A 0 rounds \<bind>
                          (\<lambda>query_chunks.
                            return
                              (F as dg composition_roots composition_bs
                                composition_final query_chunks))))))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message, rule after_alpha)
  have after_trace_final:
    "\<And>trace_bs F. hash_target_program B
      (?trace_final +
        (0 +
          (?alpha +
            (?degree +
              (0 +
                (?composition_fri +
                  (?composition_final + (0 + (?query + 0)))))))))
      (trace_final_stage A trace_bs \<bind>
        (\<lambda>trace_final. record_staged_message trace_final \<bind>
          (\<lambda>_. staged_alpha_program (length spec) \<bind>
            (\<lambda>as. degree_stage A as \<bind>
              (\<lambda>dg. record_staged_message dg \<bind>
                (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                  ceil_log (maxDegree + 1)) \<bind>
                  (\<lambda>_. staged_composition_fri_program A dg 0
                    (ceil_log (to_nat dg + 1)) [])) \<bind>
                  (\<lambda>(composition_roots, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        record_staged_message composition_final \<bind>
                          (\<lambda>_. staged_query_program A 0 rounds \<bind>
                            (\<lambda>query_chunks.
                              return
                                (F trace_final as dg composition_roots
                                  composition_bs composition_final
                                  query_chunks)))))))))))"
    by (rule hash_target_program_bind)
      (rule trace_final_target, rule after_trace_final_record)
  have after_trace_fri:
    "\<And>F. hash_target_program B
      (?trace_fri +
        (?trace_final +
          (0 +
            (?alpha +
              (?degree +
                (0 +
                  (?composition_fri +
                    (?composition_final + (0 + (?query + 0))))))))))
      (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final. record_staged_message trace_final \<bind>
              (\<lambda>_. staged_alpha_program (length spec) \<bind>
                (\<lambda>as. degree_stage A as \<bind>
                  (\<lambda>dg. record_staged_message dg \<bind>
                    (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                      ceil_log (maxDegree + 1)) \<bind>
                      (\<lambda>_. staged_composition_fri_program A dg 0
                        (ceil_log (to_nat dg + 1)) [])) \<bind>
                      (\<lambda>(composition_roots, composition_bs).
                        composition_final_stage A dg composition_bs \<bind>
                          (\<lambda>composition_final.
                            record_staged_message composition_final \<bind>
                              (\<lambda>_. staged_query_program A 0 rounds \<bind>
                                (\<lambda>query_chunks.
                                  return
                                    (F trace_roots trace_bs trace_final as dg
                                      composition_roots composition_bs
                                      composition_final query_chunks))))))))))))"
  proof (rule hash_target_program_bind)
    fix F
    show "hash_target_program B ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_target)
    fix F x
    show "hash_target_program B
      (?trace_final +
        (0 +
          (?alpha +
            (?degree +
              (0 +
                (?composition_fri +
                  (?composition_final + (0 + (?query + 0)))))))))
      (case x of (trace_roots, trace_bs) \<Rightarrow>
        trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. record_staged_message trace_final \<bind>
            (\<lambda>_. staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
    proof (cases x)
      case (Pair trace_roots trace_bs)
      have "hash_target_program B
        (?trace_final +
          (0 +
            (?alpha +
              (?degree +
                (0 +
                  (?composition_fri +
                    (?composition_final + (0 + (?query + 0)))))))))
        (trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. record_staged_message trace_final \<bind>
            (\<lambda>_. staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. staged_query_program A 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
        by (rule after_trace_final)
      then show ?thesis
        unfolding Pair by simp
    qed
  qed
  have after_trace_root_record:
    "\<And>fr F. hash_target_program B
      (0 +
        (?trace_fri +
          (?trace_final +
            (0 +
              (?alpha +
                (?degree +
                  (0 +
                    (?composition_fri +
                      (?composition_final + (0 + (?query + 0)))))))))))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final. record_staged_message trace_final \<bind>
                (\<lambda>_. staged_alpha_program (length spec) \<bind>
                  (\<lambda>as. degree_stage A as \<bind>
                    (\<lambda>dg. record_staged_message dg \<bind>
                      (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                        ceil_log (maxDegree + 1)) \<bind>
                        (\<lambda>_. staged_composition_fri_program A dg 0
                          (ceil_log (to_nat dg + 1)) [])) \<bind>
                        (\<lambda>(composition_roots, composition_bs).
                          composition_final_stage A dg composition_bs \<bind>
                            (\<lambda>composition_final.
                              record_staged_message composition_final \<bind>
                                (\<lambda>_. staged_query_program A 0 rounds \<bind>
                                  (\<lambda>query_chunks.
                                    return
                                      (F trace_roots trace_bs trace_final as dg
                                        composition_roots composition_bs
                                        composition_final query_chunks)))))))))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message, rule after_trace_fri)
  have whole:
    "hash_target_program B
      (?trace_root +
        (0 +
          (?trace_fri +
            (?trace_final +
              (0 +
                (?alpha +
                  (?degree +
                    (0 +
                      (?composition_fri +
                        (?composition_final + (0 + (?query + 0))))))))))))
      (staged_transcript_program A)"
    unfolding staged_transcript_program_def Let_def
  proof (rule hash_target_program_bind)
    show "hash_target_program B ?trace_root (trace_root_stage A)"
      by (rule trace_root_target)
    fix fr
    show "hash_target_program B
      (0 +
        (?trace_fri +
          (?trace_final +
            (0 +
              (?alpha +
                (?degree +
                  (0 +
                    (?composition_fri +
                      (?composition_final + (0 + (?query + 0)))))))))))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final.
                record_staged_message trace_final \<bind>
                  (\<lambda>_. staged_alpha_program (length spec) \<bind>
                    (\<lambda>as. degree_stage A as \<bind>
                      (\<lambda>dg. record_staged_message dg \<bind>
                        (\<lambda>_. assert (ceil_log (to_nat dg + 1) \<le>
                          ceil_log (maxDegree + 1)) \<bind>
                          (\<lambda>_. staged_composition_fri_program A dg 0
                            (ceil_log (to_nat dg + 1)) [] \<bind>
                            (\<lambda>(composition_roots, composition_bs).
                              composition_final_stage A dg composition_bs \<bind>
                                (\<lambda>composition_final.
                                  record_staged_message
                                    composition_final \<bind>
                                    (\<lambda>_. staged_query_program A 0
                                      rounds \<bind>
                                      (\<lambda>query_chunks.
                                        return
                                          \<lparr>staged_trace_root = fr,
                                           staged_trace_fri_roots =
                                            trace_roots,
                                           staged_trace_fri_challenges =
                                            trace_bs,
                                           staged_trace_final =
                                            trace_final,
                                           staged_alphas = as,
                                           staged_degree = dg,
                                           staged_composition_fri_roots =
                                            composition_roots,
                                           staged_composition_fri_challenges =
                                            composition_bs,
                                           staged_composition_final =
                                            composition_final,
                                           staged_query_chunks =
                                            query_chunks\<rparr>)))))))))))))"
      using after_trace_root_record
        [of fr
          "\<lambda>trace_roots trace_bs trace_final as dg composition_roots
              composition_bs composition_final query_chunks.
            \<lparr>staged_trace_root = fr,
             staged_trace_fri_roots = trace_roots,
             staged_trace_fri_challenges = trace_bs,
             staged_trace_final = trace_final,
             staged_alphas = as,
             staged_degree = dg,
             staged_composition_fri_roots = composition_roots,
             staged_composition_fri_challenges = composition_bs,
             staged_composition_final = composition_final,
             staged_query_chunks = query_chunks\<rparr>"]
      by (simp add: sm_bind_assoc)
  qed
  have budget_eq:
    "?trace_root +
        (0 +
          (?trace_fri +
            (?trace_final +
              (0 +
                (?alpha +
                  (?degree +
                    (0 +
                      (?composition_fri +
                        (?composition_final + (0 + (?query + 0))))))))))) =
      staged_attacker_query_budget budgets + staged_challenge_query_budget"
    unfolding staged_attacker_query_budget_def
      staged_challenge_query_budget_def
    by (simp add: add.assoc add.commute add.left_commute)
  show ?thesis
    using whole unfolding budget_eq .
qed

lemma hash_target_program_checked_staged_transcript_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (checked_staged_transcript_program A)"
proof -
  let ?trace_root = "trace_root_budget budgets"
  let ?trace_fri =
    "sum_list (trace_fri_budgets budgets) + ceil_log clength"
  let ?trace_final = "trace_final_budget budgets"
  let ?alpha = "length spec"
  let ?degree = "degree_budget budgets"
  let ?composition_fri =
    "sum_list (composition_fri_budgets budgets) +
      ceil_log (maxDegree + 1)"
  let ?composition_final = "composition_final_budget budgets"
  let ?query =
    "sum_list (query_opening_budgets budgets) + rounds"
  have trace_root_target:
    "hash_target_program B ?trace_root (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have trace_fri_target:
    "hash_target_program B ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
  proof -
    have len:
      "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_target_program B
        (sum_list
          (take (ceil_log clength)
            (drop 0 (trace_fri_budgets budgets))) +
          ceil_log clength)
        (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule hash_target_program_staged_trace_fri_program
          [OF controlled len])
    then show ?thesis
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have trace_final_target:
    "\<And>bs. hash_target_program B ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have alpha_target:
    "hash_target_program B ?alpha (staged_alpha_program (length spec))"
    by (rule hash_target_program_staged_alpha_program)
  have degree_target:
    "\<And>as. hash_target_program B ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have composition_fri_target:
    "\<And>dg. hash_target_program B ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_target_program_guarded_staged_composition_fri_program
        [OF wf controlled])
  have composition_final_target:
    "\<And>dg bs. hash_target_program B ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_target)
  have query_target:
    "\<And>trace_roots composition_roots.
      hash_target_program B ?query
        (checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
  proof -
    fix trace_roots composition_roots
    have len:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
      using wf unfolding staged_budget_wellformed_def by simp
    have exact:
      "hash_target_program B
        (sum_list
          (take rounds (drop 0 (query_opening_budgets budgets))) +
          rounds)
        (checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      by (rule hash_target_program_checked_staged_query_program
          [OF controlled len])
    then show
      "hash_target_program B ?query
        (checked_staged_query_program A trace_roots composition_roots
          0 rounds)"
      using wf unfolding staged_budget_wellformed_def by simp
  qed
  have query_tail:
    "\<And>trace_roots composition_roots F. hash_target_program B (?query + 0)
      (checked_staged_query_program A trace_roots composition_roots
        0 rounds \<bind>
        (\<lambda>query_chunks. return (F query_chunks)))"
    by (rule hash_target_program_bind)
      (rule query_target, rule hash_target_program_return)
  have after_composition_final_record:
    "\<And>trace_roots composition_roots composition_final F.
      hash_target_program B (0 + (?query + 0))
      (record_staged_message composition_final \<bind>
        (\<lambda>_. checked_staged_query_program A trace_roots
          composition_roots 0 rounds \<bind>
          (\<lambda>query_chunks. return (F query_chunks))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message, rule query_tail)
  have after_composition_final:
    "\<And>trace_roots dg composition_roots bs F. hash_target_program B
      (?composition_final + (0 + (?query + 0)))
      (composition_final_stage A dg bs \<bind>
        (\<lambda>composition_final.
          record_staged_message composition_final \<bind>
            (\<lambda>_. checked_staged_query_program A trace_roots
              composition_roots 0 rounds \<bind>
              (\<lambda>query_chunks.
                return (F composition_final query_chunks)))))"
    by (rule hash_target_program_bind)
      (rule composition_final_target, rule after_composition_final_record)
  have after_composition_fri:
    "\<And>trace_roots dg F. hash_target_program B
      (?composition_fri +
        (?composition_final + (0 + (?query + 0))))
      ((assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) [])) \<bind>
        (\<lambda>(composition_roots, composition_bs).
          composition_final_stage A dg composition_bs \<bind>
            (\<lambda>composition_final.
              record_staged_message composition_final \<bind>
                (\<lambda>_. checked_staged_query_program A trace_roots
                  composition_roots 0 rounds \<bind>
                  (\<lambda>query_chunks.
                    return
                      (F composition_roots composition_bs composition_final
                        query_chunks))))))"
  proof (rule hash_target_program_bind)
    fix trace_roots dg F
    show "hash_target_program B ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
      by (rule composition_fri_target)
  next
    fix trace_roots dg F x
    show "hash_target_program B
      (?composition_final + (0 + (?query + 0)))
      (case x of (composition_roots, composition_bs) \<Rightarrow>
        composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. checked_staged_query_program A trace_roots
                composition_roots 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
    proof (cases x)
      case (Pair composition_roots composition_bs)
      have "hash_target_program B
        (?composition_final + (0 + (?query + 0)))
        (composition_final_stage A dg composition_bs \<bind>
          (\<lambda>composition_final.
            record_staged_message composition_final \<bind>
              (\<lambda>_. checked_staged_query_program A trace_roots
                composition_roots 0 rounds \<bind>
                (\<lambda>query_chunks.
                  return
                    (F composition_roots composition_bs composition_final
                      query_chunks)))))"
        by (rule after_composition_final)
      then show ?thesis
        unfolding Pair by simp
    qed
  qed
  have after_degree_record:
    "\<And>trace_roots dg F. hash_target_program B
      (0 +
        (?composition_fri +
          (?composition_final + (0 + (?query + 0)))))
      (record_staged_message dg \<bind>
        (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
          ceil_log (maxDegree + 1)) \<bind>
          (\<lambda>_. staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) [])) \<bind>
          (\<lambda>(composition_roots, composition_bs).
            composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                  (\<lambda>_. checked_staged_query_program A trace_roots
                    composition_roots 0 rounds \<bind>
                    (\<lambda>query_chunks.
                      return
                        (F composition_roots composition_bs composition_final
                          query_chunks)))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message,
        rule after_composition_fri)
  have after_degree:
    "\<And>trace_roots as F. hash_target_program B
      (?degree +
        (0 +
          (?composition_fri +
            (?composition_final + (0 + (?query + 0))))))
      (degree_stage A as \<bind>
        (\<lambda>dg. record_staged_message dg \<bind>
          (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
            ceil_log (maxDegree + 1)) \<bind>
            (\<lambda>_. staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) [])) \<bind>
            (\<lambda>(composition_roots, composition_bs).
              composition_final_stage A dg composition_bs \<bind>
                (\<lambda>composition_final.
                  record_staged_message composition_final \<bind>
                    (\<lambda>_. checked_staged_query_program A trace_roots
                      composition_roots 0 rounds \<bind>
                      (\<lambda>query_chunks.
                        return
                          (F dg composition_roots composition_bs
                            composition_final query_chunks))))))))"
    by (rule hash_target_program_bind)
      (rule degree_target, rule after_degree_record)
  have after_alpha:
    "\<And>trace_roots F. hash_target_program B
      (?alpha +
        (?degree +
          (0 +
            (?composition_fri +
              (?composition_final + (0 + (?query + 0)))))))
      (staged_alpha_program (length spec) \<bind>
        (\<lambda>as. degree_stage A as \<bind>
          (\<lambda>dg. record_staged_message dg \<bind>
            (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
              ceil_log (maxDegree + 1)) \<bind>
              (\<lambda>_. staged_composition_fri_program A dg 0
                (ceil_log (to_nat dg + 1)) [])) \<bind>
              (\<lambda>(composition_roots, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                      (\<lambda>_. checked_staged_query_program A trace_roots
                        composition_roots 0 rounds \<bind>
                        (\<lambda>query_chunks.
                          return
                            (F as dg composition_roots composition_bs
                              composition_final query_chunks)))))))))"
    by (rule hash_target_program_bind)
      (rule alpha_target, rule after_degree)
  have after_trace_final_record:
    "\<And>trace_roots trace_final F. hash_target_program B
      (0 +
        (?alpha +
          (?degree +
            (0 +
              (?composition_fri +
                (?composition_final + (0 + (?query + 0))))))))
      (record_staged_message trace_final \<bind>
        (\<lambda>_. staged_alpha_program (length spec) \<bind>
          (\<lambda>as. degree_stage A as \<bind>
            (\<lambda>dg. record_staged_message dg \<bind>
              (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1)) \<bind>
                (\<lambda>_. staged_composition_fri_program A dg 0
                  (ceil_log (to_nat dg + 1)) [])) \<bind>
                (\<lambda>(composition_roots, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                        (\<lambda>_. checked_staged_query_program A trace_roots
                          composition_roots 0 rounds \<bind>
                          (\<lambda>query_chunks.
                            return
                              (F as dg composition_roots composition_bs
                                composition_final query_chunks))))))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message, rule after_alpha)
  have after_trace_final:
    "\<And>trace_roots trace_bs F. hash_target_program B
      (?trace_final +
        (0 +
          (?alpha +
            (?degree +
              (0 +
                (?composition_fri +
                  (?composition_final + (0 + (?query + 0)))))))))
      (trace_final_stage A trace_bs \<bind>
        (\<lambda>trace_final. record_staged_message trace_final \<bind>
          (\<lambda>_. staged_alpha_program (length spec) \<bind>
            (\<lambda>as. degree_stage A as \<bind>
              (\<lambda>dg. record_staged_message dg \<bind>
                (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                  ceil_log (maxDegree + 1)) \<bind>
                  (\<lambda>_. staged_composition_fri_program A dg 0
                    (ceil_log (to_nat dg + 1)) [])) \<bind>
                  (\<lambda>(composition_roots, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        record_staged_message composition_final \<bind>
                          (\<lambda>_. checked_staged_query_program A trace_roots
                            composition_roots 0 rounds \<bind>
                            (\<lambda>query_chunks.
                              return
                                (F trace_final as dg composition_roots
                                  composition_bs composition_final
                                  query_chunks)))))))))))"
    by (rule hash_target_program_bind)
      (rule trace_final_target, rule after_trace_final_record)
  have after_trace_fri:
    "\<And>F. hash_target_program B
      (?trace_fri +
        (?trace_final +
          (0 +
            (?alpha +
              (?degree +
                (0 +
                  (?composition_fri +
                    (?composition_final + (0 + (?query + 0))))))))))
      (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
        (\<lambda>(trace_roots, trace_bs).
          trace_final_stage A trace_bs \<bind>
            (\<lambda>trace_final. record_staged_message trace_final \<bind>
              (\<lambda>_. staged_alpha_program (length spec) \<bind>
                (\<lambda>as. degree_stage A as \<bind>
                  (\<lambda>dg. record_staged_message dg \<bind>
                    (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                      ceil_log (maxDegree + 1)) \<bind>
                      (\<lambda>_. staged_composition_fri_program A dg 0
                        (ceil_log (to_nat dg + 1)) [])) \<bind>
                      (\<lambda>(composition_roots, composition_bs).
                        composition_final_stage A dg composition_bs \<bind>
                          (\<lambda>composition_final.
                            record_staged_message composition_final \<bind>
                              (\<lambda>_. checked_staged_query_program A
                                trace_roots composition_roots 0 rounds \<bind>
                                (\<lambda>query_chunks.
                                  return
                                    (F trace_roots trace_bs trace_final as dg
                                      composition_roots composition_bs
                                      composition_final query_chunks))))))))))))"
  proof (rule hash_target_program_bind)
    fix F
    show "hash_target_program B ?trace_fri
      (staged_trace_fri_program A 0 (ceil_log clength) [])"
      by (rule trace_fri_target)
  next
    fix F x
    show "hash_target_program B
      (?trace_final +
        (0 +
          (?alpha +
            (?degree +
              (0 +
                (?composition_fri +
                  (?composition_final + (0 + (?query + 0)))))))))
      (case x of (trace_roots, trace_bs) \<Rightarrow>
        trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. record_staged_message trace_final \<bind>
            (\<lambda>_. staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. checked_staged_query_program A
                              trace_roots composition_roots 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
    proof (cases x)
      case (Pair trace_roots trace_bs)
      have "hash_target_program B
        (?trace_final +
          (0 +
            (?alpha +
              (?degree +
                (0 +
                  (?composition_fri +
                    (?composition_final + (0 + (?query + 0)))))))))
        (trace_final_stage A trace_bs \<bind>
          (\<lambda>trace_final. record_staged_message trace_final \<bind>
            (\<lambda>_. staged_alpha_program (length spec) \<bind>
              (\<lambda>as. degree_stage A as \<bind>
                (\<lambda>dg. record_staged_message dg \<bind>
                  (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                    ceil_log (maxDegree + 1)) \<bind>
                    (\<lambda>_. staged_composition_fri_program A dg 0
                      (ceil_log (to_nat dg + 1)) [])) \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                            (\<lambda>_. checked_staged_query_program A
                              trace_roots composition_roots 0 rounds \<bind>
                              (\<lambda>query_chunks.
                                return
                                  (F trace_roots trace_bs trace_final as dg
                                    composition_roots composition_bs
                                    composition_final query_chunks)))))))))))"
        by (rule after_trace_final)
      then show ?thesis
        unfolding Pair by simp
    qed
  qed
  have after_trace_root_record:
    "\<And>fr F. hash_target_program B
      (0 +
        (?trace_fri +
          (?trace_final +
            (0 +
              (?alpha +
                (?degree +
                  (0 +
                    (?composition_fri +
                      (?composition_final + (0 + (?query + 0)))))))))))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final. record_staged_message trace_final \<bind>
                (\<lambda>_. staged_alpha_program (length spec) \<bind>
                  (\<lambda>as. degree_stage A as \<bind>
                    (\<lambda>dg. record_staged_message dg \<bind>
                      (\<lambda>_. (assert (ceil_log (to_nat dg + 1) \<le>
                        ceil_log (maxDegree + 1)) \<bind>
                        (\<lambda>_. staged_composition_fri_program A dg 0
                          (ceil_log (to_nat dg + 1)) [])) \<bind>
                        (\<lambda>(composition_roots, composition_bs).
                          composition_final_stage A dg composition_bs \<bind>
                            (\<lambda>composition_final.
                              record_staged_message composition_final \<bind>
                                (\<lambda>_. checked_staged_query_program A
                                  trace_roots composition_roots 0 rounds \<bind>
                                  (\<lambda>query_chunks.
                                    return
                                      (F trace_roots trace_bs trace_final as dg
                                        composition_roots composition_bs
                                        composition_final query_chunks)))))))))))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_record_staged_message, rule after_trace_fri)
  have whole:
    "hash_target_program B
      (?trace_root +
        (0 +
          (?trace_fri +
            (?trace_final +
              (0 +
                (?alpha +
                  (?degree +
                    (0 +
                      (?composition_fri +
                        (?composition_final + (0 + (?query + 0))))))))))))
      (checked_staged_transcript_program A)"
    unfolding checked_staged_transcript_program_def Let_def
  proof (rule hash_target_program_bind)
    show "hash_target_program B ?trace_root (trace_root_stage A)"
      by (rule trace_root_target)
  next
    fix fr
    show "hash_target_program B
      (0 +
        (?trace_fri +
          (?trace_final +
            (0 +
              (?alpha +
                (?degree +
                  (0 +
                    (?composition_fri +
                      (?composition_final + (0 + (?query + 0)))))))))))
      (record_staged_message fr \<bind>
        (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
          (\<lambda>(trace_roots, trace_bs).
            trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final.
                record_staged_message trace_final \<bind>
                  (\<lambda>_. staged_alpha_program (length spec) \<bind>
                    (\<lambda>as. degree_stage A as \<bind>
                      (\<lambda>dg. record_staged_message dg \<bind>
                        (\<lambda>_. assert (ceil_log (to_nat dg + 1) \<le>
                          ceil_log (maxDegree + 1)) \<bind>
                          (\<lambda>_. staged_composition_fri_program A dg 0
                            (ceil_log (to_nat dg + 1)) [] \<bind>
                            (\<lambda>(composition_roots, composition_bs).
                              composition_final_stage A dg composition_bs \<bind>
                                (\<lambda>composition_final.
                                  record_staged_message
                                    composition_final \<bind>
                                    (\<lambda>_. checked_staged_query_program A
                                      trace_roots composition_roots 0
                                      rounds \<bind>
                                      (\<lambda>query_chunks.
                                        return
                                          \<lparr>staged_trace_root = fr,
                                           staged_trace_fri_roots =
                                            trace_roots,
                                           staged_trace_fri_challenges =
                                            trace_bs,
                                           staged_trace_final =
                                            trace_final,
                                           staged_alphas = as,
                                           staged_degree = dg,
                                           staged_composition_fri_roots =
                                            composition_roots,
                                           staged_composition_fri_challenges =
                                            composition_bs,
                                           staged_composition_final =
                                            composition_final,
                                           staged_query_chunks =
                                            query_chunks\<rparr>)))))))))))))"
      using after_trace_root_record
        [of fr
          "\<lambda>trace_roots trace_bs trace_final as dg composition_roots
              composition_bs composition_final query_chunks.
            \<lparr>staged_trace_root = fr,
             staged_trace_fri_roots = trace_roots,
             staged_trace_fri_challenges = trace_bs,
             staged_trace_final = trace_final,
             staged_alphas = as,
             staged_degree = dg,
             staged_composition_fri_roots = composition_roots,
             staged_composition_fri_challenges = composition_bs,
             staged_composition_final = composition_final,
             staged_query_chunks = query_chunks\<rparr>"]
      by (simp add: sm_bind_assoc)
  qed
  have budget_eq:
    "?trace_root +
        (0 +
          (?trace_fri +
            (?trace_final +
              (0 +
                (?alpha +
                  (?degree +
                    (0 +
                      (?composition_fri +
                        (?composition_final + (0 + (?query + 0))))))))))) =
      staged_attacker_query_budget budgets + staged_challenge_query_budget"
    unfolding staged_attacker_query_budget_def
      staged_challenge_query_budget_def
    by (simp add: add.assoc add.commute add.left_commute)
  show ?thesis
    using whole unfolding budget_eq .
qed

lemma hash_target_program_staged_semantic_adversary:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (staged_semantic_adversary A)"
proof -
  have "hash_target_program B
    ((staged_attacker_query_budget budgets + staged_challenge_query_budget) +
      0)
    (staged_semantic_adversary A)"
    unfolding staged_semantic_adversary_def
  proof (rule hash_target_program_bind
      [where n="staged_attacker_query_budget budgets +
        staged_challenge_query_budget" and n'=0])
    show "hash_target_program B
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (staged_transcript_program A)"
      by (rule hash_target_program_staged_transcript_program[OF wf controlled])
    show "\<And>x. hash_target_program B 0
      (return (staged_proof_transcript x))"
      by (rule hash_target_program_return)
  qed
  then show ?thesis by simp
qed

lemma hash_extension_preserving_staged_semantic_adversary:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows "hash_extension_preserving (staged_semantic_adversary A)"
  by (rule hash_target_program_extension
      [OF hash_target_program_staged_semantic_adversary
        [OF wf controlled, of "{}"]])

lemma admissible_staged_semantic_adversary:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "admissible_adversary
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (staged_semantic_adversary A)"
  unfolding admissible_adversary_def
proof (intro conjI allI)
  show "hash_extension_preserving (staged_semantic_adversary A)"
    by (rule hash_extension_preserving_staged_semantic_adversary
        [OF wf controlled])
  show "hash_range_budget
    (staged_attacker_query_budget budgets + staged_challenge_query_budget)
    (staged_semantic_adversary A)"
    by (rule hash_range_budget_staged_semantic_adversary[OF wf controlled])
  show "hash_collision_budget
    (staged_attacker_query_budget budgets + staged_challenge_query_budget)
    (staged_semantic_adversary A)"
    by (rule hash_collision_budget_staged_semantic_adversary
        [OF wf controlled])
  fix B
  show "hash_target_program B
    (staged_attacker_query_budget budgets + staged_challenge_query_budget)
    (staged_semantic_adversary A)"
    by (rule hash_target_program_staged_semantic_adversary[OF wf controlled])
qed

lemma staged_trace_fri_program_Suc_outcomeE:
  assumes outcome:
    "Some ((roots, bs'), t) \<in>
      set_dist (execute (staged_trace_fri_program A i (Suc n) bs) s)"
  obtains root b roots' s1 s2 s3 where
    "Some (root, s1) \<in>
      set_dist (execute (trace_fri_root_stage A i bs) s)"
    "Some ((), s2) \<in>
      set_dist (execute (record_staged_message root) s1)"
    "Some (b, s3) \<in>
      set_dist (execute receive_trace_fri_challenge s2)"
    "Some ((roots', bs'), t) \<in>
      set_dist
        (execute
          (staged_trace_fri_program A (Suc i) n (bs @ [b])) s3)"
    "roots = root # roots'"
  using outcome
  by (auto elim!: set_dist_bindE intro: that)

lemma staged_composition_fri_program_Suc_outcomeE:
  assumes outcome:
    "Some ((roots, bs'), t) \<in>
      set_dist
        (execute
          (staged_composition_fri_program A dg i (Suc n) bs) s)"
  obtains root b roots' s1 s2 s3 where
    "Some (root, s1) \<in>
      set_dist (execute (composition_fri_root_stage A dg i bs) s)"
    "Some ((), s2) \<in>
      set_dist (execute (record_staged_message root) s1)"
    "Some (b, s3) \<in>
      set_dist (execute receive_composition_fri_challenge s2)"
    "Some ((roots', bs'), t) \<in>
      set_dist
        (execute
          (staged_composition_fri_program
            A dg (Suc i) n (bs @ [b])) s3)"
    "roots = root # roots'"
  using outcome
  by (auto elim!: set_dist_bindE intro: that)

lemma staged_alpha_program_Suc_outcomeE:
  assumes outcome:
    "Some (as, t) \<in>
      set_dist (execute (staged_alpha_program (Suc n)) s)"
  obtains a as' s1 s2 where
    "Some (a, s1) \<in>
      set_dist (execute receive_alpha_challenge s)"
    "Some ((), s2) \<in>
      set_dist (execute (record_staged_message a) s1)"
    "Some (as', t) \<in>
      set_dist (execute (staged_alpha_program n) s2)"
    "as = a # as'"
  using outcome
  by (auto elim!: set_dist_bindE intro: that)

lemma staged_query_program_Suc_outcomeE:
  assumes outcome:
    "Some (chunks, t) \<in>
      set_dist (execute (staged_query_program A i (Suc n)) s)"
  obtains raw chunk chunks' s1 s2 s3 where
    "Some (raw, s1) \<in>
      set_dist (execute receive_query_index_challenge s)"
    "Some (chunk, s2) \<in>
      set_dist (execute (query_opening_stage A i raw) s1)"
    "Some ((), s3) \<in>
      set_dist (execute (record_staged_messages chunk) s2)"
    "Some (chunks', t) \<in>
      set_dist (execute (staged_query_program A (Suc i) n) s3)"
    "chunks = chunk # chunks'"
  using outcome
  by (auto elim!: set_dist_bindE intro: that)

lemma checked_staged_query_program_Suc_outcomeE:
  assumes outcome:
    "Some (chunks, t) \<in>
      set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            i (Suc n)) s)"
  obtains raw chunk chunks' s1 s2 s3 where
    "Some (raw, s1) \<in>
      set_dist (execute receive_query_index_challenge s)"
    "Some (chunk, s2) \<in>
      set_dist (execute (query_opening_stage A i raw) s1)"
    "verifier_query_round_chunk (index (to_nat raw))
      trace_roots composition_roots chunk"
    "Some ((), s3) \<in>
      set_dist (execute (record_staged_messages chunk) s2)"
    "Some (chunks', t) \<in>
      set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            (Suc i) n) s3)"
    "chunks = chunk # chunks'"
  using outcome
  unfolding checked_staged_query_program.simps assert_def Let_def
  by (auto simp: throw_no_outcome elim!: set_dist_bindE intro: that
      split: if_splits)

lemma checked_staged_query_program_outcome_imp_staged_query_program:
  assumes outcome:
    "Some (chunks, t) \<in>
      set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            i n) s)"
  shows
    "Some (chunks, t) \<in>
      set_dist (execute (staged_query_program A i n) s)"
  using outcome
proof (induction n arbitrary: i chunks s t)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  obtain raw chunk chunks' s1 s2 s3 where
    challenge_out:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and stage_out:
      "Some (chunk, s2) \<in>
        set_dist (execute (query_opening_stage A i raw) s1)"
    and record_out:
      "Some ((), s3) \<in>
        set_dist (execute (record_staged_messages chunk) s2)"
    and rest_out:
      "Some (chunks', t) \<in>
        set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
  proof (rule checked_staged_query_program_Suc_outcomeE[OF Suc.prems])
    fix raw chunk chunks' s1 s2 s3
    assume challenge:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge s)"
      and stage:
        "Some (chunk, s2) \<in>
          set_dist (execute (query_opening_stage A i raw) s1)"
      and recorded:
        "Some ((), s3) \<in>
          set_dist (execute (record_staged_messages chunk) s2)"
      and rest:
        "Some (chunks', t) \<in>
          set_dist
            (execute
              (checked_staged_query_program A trace_roots composition_roots
                (Suc i) n) s3)"
      and chunks: "chunks = chunk # chunks'"
    show ?thesis
      by (rule that[OF challenge stage recorded rest chunks])
  qed
  have rest_unchecked:
    "Some (chunks', t) \<in>
      set_dist (execute (staged_query_program A (Suc i) n) s3)"
    by (rule Suc.IH[OF rest_out])
  show ?case
    unfolding chunks_eq staged_query_program.simps
    by (intro set_dist_bindI[OF challenge_out]
        set_dist_bindI[OF stage_out]
        set_dist_bindI[OF record_out]
        set_dist_bindI[OF rest_unchecked])
      simp
qed

lemma checked_staged_transcript_program_outcome_imp_staged_transcript_program:
  assumes outcome:
    "Some (data, t) \<in>
      set_dist
        (execute (checked_staged_transcript_program A) s)"
  shows
    "Some (data, t) \<in>
      set_dist (execute (staged_transcript_program A) s)"
  using outcome
  unfolding checked_staged_transcript_program_def staged_transcript_program_def
    Let_def
  by (auto elim!: set_dist_bindE
      intro!: set_dist_bindI
      intro: checked_staged_query_program_outcome_imp_staged_query_program
      split: prod.splits)

lemma
  checked_staged_query_challenge_prefix_outcome_imp_staged_query_prefix:
  assumes outcome:
    "Some (prefix, t) \<in>
      set_dist
        (execute (checked_staged_query_challenge_prefix_program A i) s)"
  shows
    "Some ((sqp_degree prefix, sqp_composition_final prefix,
        sqp_query_chunks prefix), t) \<in>
      set_dist (execute (staged_query_challenge_prefix_program A i) s)"
  using outcome
  unfolding checked_staged_query_challenge_prefix_program_def
    staged_query_challenge_prefix_program_def Let_def
  by (auto elim!: set_dist_bindE
      intro!: set_dist_bindI
      intro: checked_staged_query_program_outcome_imp_staged_query_program
      split: prod.splits)

lemma checked_staged_query_program_wp_event_le_staged:
  assumes none: "\<not> P None"
  shows
    "wp_event
      (checked_staged_query_program A trace_roots composition_roots i n)
      P s \<le>
     wp_event (staged_query_program A i n) P s"
  using none
proof (induction n arbitrary: i s P)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?checked =
    "checked_staged_query_program A trace_roots composition_roots i (Suc n)"
  let ?plain = "staged_query_program A i (Suc n)"
  show ?case
    unfolding checked_staged_query_program.simps
      staged_query_program.simps Let_def
  proof (rule wp_event_bind_mono_cont)
    show "P None \<Longrightarrow> P None" .
  next
    fix raw s1
    assume raw_out:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge s)"
    show
      "wp_event
        (query_opening_stage A i raw \<bind>
          (\<lambda>chunk.
            assert
              (verifier_query_round_chunk (index (to_nat raw))
                trace_roots composition_roots chunk) \<bind>
            (\<lambda>_.
              record_staged_messages chunk \<bind>
              (\<lambda>_.
                checked_staged_query_program A trace_roots
                  composition_roots (Suc i) n \<bind>
                (\<lambda>chunks. return (chunk # chunks))))))
        P s1
       \<le>
       wp_event
        (query_opening_stage A i raw \<bind>
          (\<lambda>chunk.
            record_staged_messages chunk \<bind>
            (\<lambda>_.
              staged_query_program A (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks)))))
        P s1"
    proof (rule wp_event_bind_mono_cont)
      show "P None \<Longrightarrow> P None" .
    next
      fix chunk s2
      assume chunk_out:
        "Some (chunk, s2) \<in>
          set_dist (execute (query_opening_stage A i raw) s1)"
      let ?tailP =
        "\<lambda>out. case out of None \<Rightarrow> P None
          | Some (chunks, t) \<Rightarrow> P (Some (chunk # chunks, t))"
      have tail_none: "\<not> ?tailP None"
        using Suc.prems by simp
      have checked_tail_le:
        "\<And>s'.
        wp_event
          (checked_staged_query_program A trace_roots composition_roots
            (Suc i) n)
          ?tailP s'
         \<le>
         wp_event (staged_query_program A (Suc i) n) ?tailP s'"
        by (rule Suc.IH) (rule tail_none)
      have after_record:
        "wp_event
          (record_staged_messages chunk \<bind>
            (\<lambda>_.
              checked_staged_query_program A trace_roots
                composition_roots (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks))))
          P s2
         \<le>
         wp_event
          (record_staged_messages chunk \<bind>
            (\<lambda>_.
              staged_query_program A (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks))))
          P s2"
      proof (rule wp_event_bind_mono_cont)
        show "P None \<Longrightarrow> P None" .
      next
        fix u s3
        assume "Some (u, s3) \<in>
          set_dist (execute (record_staged_messages chunk) s2)"
        show
          "wp_event
            (checked_staged_query_program A trace_roots composition_roots
              (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks)))
            P s3
           \<le>
           wp_event
            (staged_query_program A (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks)))
            P s3"
          unfolding wp_event_bind_return_map
          using checked_tail_le[of s3]
          by simp
      qed
      have checked_assert:
        "wp_event
          (assert
            (verifier_query_round_chunk (index (to_nat raw))
              trace_roots composition_roots chunk) \<bind>
            (\<lambda>_.
              record_staged_messages chunk \<bind>
              (\<lambda>_.
                checked_staged_query_program A trace_roots
                  composition_roots (Suc i) n \<bind>
                (\<lambda>chunks. return (chunk # chunks)))))
          P s2
         \<le>
         wp_event
          (record_staged_messages chunk \<bind>
            (\<lambda>_.
              checked_staged_query_program A trace_roots
                composition_roots (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks))))
          P s2"
        by (rule wp_event_assert_bind_le) (rule Suc.prems)
      show
        "wp_event
          (assert
            (verifier_query_round_chunk (index (to_nat raw))
              trace_roots composition_roots chunk) \<bind>
            (\<lambda>_.
              record_staged_messages chunk \<bind>
              (\<lambda>_.
                checked_staged_query_program A trace_roots
                  composition_roots (Suc i) n \<bind>
                (\<lambda>chunks. return (chunk # chunks)))))
          P s2
         \<le>
         wp_event
          (record_staged_messages chunk \<bind>
            (\<lambda>_.
              staged_query_program A (Suc i) n \<bind>
              (\<lambda>chunks. return (chunk # chunks))))
          P s2"
        by (rule order_trans[OF checked_assert after_record])
    qed
  qed
qed

lemma checked_staged_transcript_program_wp_event_le_staged:
  assumes none: "\<not> P None"
  shows
    "wp_event (checked_staged_transcript_program A) P s \<le>
     wp_event (staged_transcript_program A) P s"
  unfolding checked_staged_transcript_program_def staged_transcript_program_def
    Let_def
  apply (rule wp_event_bind_mono_cont)
   apply simp
  apply (rename_tac fr s1)
  apply (rule wp_event_bind_mono_cont)
   apply simp
  apply (rename_tac u1 s2)
  apply (rule wp_event_bind_mono_cont)
   apply simp
  apply (rename_tac trace_pair s3)
  apply (case_tac trace_pair)
  apply (rename_tac trace_roots trace_bs)
  apply simp
  apply (rule wp_event_bind_mono_cont)
   apply simp
  apply (rename_tac trace_final s4)
  apply (rule wp_event_bind_mono_cont)
   apply simp
  apply (rename_tac u2 s5)
  apply (rule wp_event_bind_mono_cont)
   apply simp
  apply (rename_tac as s6)
  apply (rule wp_event_bind_mono_cont)
   apply simp
  apply (rename_tac dg s7)
  apply (rule wp_event_bind_mono_cont)
   apply simp
  apply (rename_tac u3 s8)
  apply (rule wp_event_bind_mono_cont)
   apply simp
  apply (rename_tac u4 s9)
  apply (rule wp_event_bind_mono_cont)
   apply simp
  apply (rename_tac composition_pair s10)
  apply (case_tac composition_pair)
  apply (rename_tac composition_roots composition_bs)
  apply simp
  apply (rule wp_event_bind_mono_cont)
   apply simp
  apply (rename_tac composition_final s11)
  apply (rule wp_event_bind_mono_cont)
   apply simp
  apply (rename_tac u5 s12)
  apply (subst wp_event_bind_return_map)
  apply (subst wp_event_bind_return_map)
  apply (rule checked_staged_query_program_wp_event_le_staged)
  apply (simp add: none)
  done

lemma hash_range_budget_checked_staged_query_challenge_prefix_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "hash_range_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_challenge_prefix_program A i)"
  unfolding hash_range_budget_def
proof (intro allI impI)
  fix s prefix t
  assume outcome:
    "Some (prefix, t) \<in>
      set_dist
        (execute (checked_staged_query_challenge_prefix_program A i) s)"
  have unchecked_out:
    "Some ((sqp_degree prefix, sqp_composition_final prefix,
        sqp_query_chunks prefix), t) \<in>
      set_dist (execute (staged_query_challenge_prefix_program A i) s)"
    by (rule checked_staged_query_challenge_prefix_outcome_imp_staged_query_prefix
        [OF outcome])
  have budget:
    "hash_range_budget
      (staged_query_search_queries budgets i)
      (staged_query_challenge_prefix_program A i)"
    by (rule hash_range_budget_staged_query_challenge_prefix_program
        [OF wf controlled i_bound])
  show "card (hash_map_output_values t)
      \<le> card (hash_map_output_values s) +
        staged_query_search_queries budgets i"
    using budget unchecked_out unfolding hash_range_budget_def by blast
qed

lemma hash_collision_budget_checked_staged_query_challenge_prefix_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "hash_collision_budget
      (staged_query_search_queries budgets i)
      (checked_staged_query_challenge_prefix_program A i)"
  unfolding hash_collision_budget_def
proof (intro allI impI)
  fix s :: "'f protocol_channel"
  assume clean: "\<not> hash_map_output_collision s"
  have checked_le:
    "wp_event (checked_staged_query_challenge_prefix_program A i)
      (hash_new_collision_event s) s \<le>
     wp_event (staged_query_challenge_prefix_program A i)
      (hash_new_collision_event s) s"
    unfolding checked_staged_query_challenge_prefix_program_def
      staged_query_challenge_prefix_program_def Let_def
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_collision_event_def)
    apply (rename_tac alpha_prefix s1)
    apply (case_tac alpha_prefix)
    apply (rename_tac fr trace_roots trace_bs trace_final)
    apply simp
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_collision_event_def)
    apply (rename_tac as s2)
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_collision_event_def)
    apply (rename_tac dg s3)
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_collision_event_def)
    apply (rename_tac u s4)
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_collision_event_def)
    apply (rename_tac u2 s5)
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_collision_event_def)
    apply (rename_tac composition_pair s6)
    apply (case_tac composition_pair)
    apply (rename_tac composition_roots composition_bs)
    apply simp
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_collision_event_def)
    apply (rename_tac composition_final s7)
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_collision_event_def)
    apply (rename_tac u3 s8)
    apply (subst wp_event_bind_return_map)
    apply (subst wp_event_bind_return_map)
    apply (simp add: hash_new_collision_event_def)
    apply (rule checked_staged_query_program_wp_event_le_staged)
    apply (simp add: hash_new_collision_event_def)
    done
  have unchecked_bound:
    "wp_event (staged_query_challenge_prefix_program A i)
      (hash_new_collision_event s) s \<le>
      hash_collision_budget_value (card (hash_map_output_values s))
        (staged_query_search_queries budgets i)"
    using hash_collision_budget_staged_query_challenge_prefix_program
        [OF wf controlled i_bound] clean
    unfolding hash_collision_budget_def by blast
  show "wp_event (checked_staged_query_challenge_prefix_program A i)
      (hash_new_collision_event s) s
    \<le> hash_collision_budget_value (card (hash_map_output_values s))
        (staged_query_search_queries budgets i)"
    by (rule order_trans[OF checked_le unchecked_bound])
qed

lemma hash_range_budget_checked_staged_transcript_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (checked_staged_transcript_program A)"
  unfolding hash_range_budget_def
proof (intro allI impI)
  fix s data t
  assume outcome:
    "Some (data, t) \<in>
      set_dist (execute (checked_staged_transcript_program A) s)"
  have unchecked_out:
    "Some (data, t) \<in> set_dist (execute (staged_transcript_program A) s)"
    by (rule checked_staged_transcript_program_outcome_imp_staged_transcript_program
        [OF outcome])
  have budget:
    "hash_range_budget
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (staged_transcript_program A)"
    by (rule hash_range_budget_staged_transcript_program[OF wf controlled])
  show "card (hash_map_output_values t)
      \<le> card (hash_map_output_values s) +
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    using budget unchecked_out unfolding hash_range_budget_def by blast
qed

lemma hash_collision_budget_checked_staged_transcript_program:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_collision_budget
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (checked_staged_transcript_program A)"
  unfolding hash_collision_budget_def
proof (intro allI impI)
  fix s :: "'f protocol_channel"
  assume clean: "\<not> hash_map_output_collision s"
  let ?budget =
    "staged_attacker_query_budget budgets + staged_challenge_query_budget"
  have checked_le:
    "wp_event (checked_staged_transcript_program A)
      (hash_new_collision_event s) s \<le>
     wp_event (staged_transcript_program A)
      (hash_new_collision_event s) s"
    by (rule checked_staged_transcript_program_wp_event_le_staged)
      (simp add: hash_new_collision_event_def)
  have unchecked_bound:
    "wp_event (staged_transcript_program A)
      (hash_new_collision_event s) s \<le>
      hash_collision_budget_value (card (hash_map_output_values s)) ?budget"
    using hash_collision_budget_staged_transcript_program[OF wf controlled]
      clean
    unfolding hash_collision_budget_def by blast
  show "wp_event (checked_staged_transcript_program A)
      (hash_new_collision_event s) s
    \<le> hash_collision_budget_value (card (hash_map_output_values s)) ?budget"
    by (rule order_trans[OF checked_le unchecked_bound])
qed

lemma checked_staged_query_prefix_target_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_challenge_prefix_program A i)
      (hash_new_output_hit_event B s) s \<le>
      staged_phase_target_error B
        (staged_query_search_queries budgets i)"
proof -
  have checked_le_unchecked:
    "wp_event (checked_staged_query_challenge_prefix_program A i)
      (hash_new_output_hit_event B s) s \<le>
     wp_event (staged_query_challenge_prefix_program A i)
      (hash_new_output_hit_event B s) s"
    unfolding checked_staged_query_challenge_prefix_program_def
      staged_query_challenge_prefix_program_def Let_def
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_output_hit_event_def)
    apply (rename_tac alpha_prefix s1)
    apply (case_tac alpha_prefix)
    apply (rename_tac fr trace_roots trace_bs trace_final)
    apply simp
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_output_hit_event_def)
    apply (rename_tac as s2)
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_output_hit_event_def)
    apply (rename_tac dg s3)
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_output_hit_event_def)
    apply (rename_tac u s4)
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_output_hit_event_def)
    apply (rename_tac u2 s5)
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_output_hit_event_def)
    apply (rename_tac composition_pair s6)
    apply (case_tac composition_pair)
    apply (rename_tac composition_roots composition_bs)
    apply simp
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_output_hit_event_def)
    apply (rename_tac composition_final s7)
    apply (rule wp_event_bind_mono_cont)
     apply (simp add: hash_new_output_hit_event_def)
    apply (rename_tac u3 s8)
    apply (subst wp_event_bind_return_map)
    apply (subst wp_event_bind_return_map)
    apply (simp add: hash_new_output_hit_event_def)
    apply (rule checked_staged_query_program_wp_event_le_staged)
    apply simp
    done
  also have "... \<le>
      staged_phase_target_error B
        (staged_query_search_queries budgets i)"
    by (rule staged_query_prefix_target_hit_bound[OF wf controlled i_bound])
  finally show ?thesis .
qed

lemma checked_staged_query_prefix_bad_index_target_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_challenge_prefix_program A i)
      (hash_new_output_hit_event (query_index_raw_preimage B) s) s \<le>
      staged_query_prefix_bad_index_error budgets B i"
  unfolding staged_query_prefix_bad_index_error_def
  by (rule checked_staged_query_prefix_target_hit_bound
      [OF wf controlled i_bound])

end

end
