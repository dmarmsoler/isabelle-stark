(*  Title:      Stark/Soundness_FRI_Query_Aware_Interface.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Query_Aware_Interface
  imports Soundness_FRI_Sampled_Interface
begin

text \<open>
  Query-aware sampled FRI interface.

  This theory names the joint query/challenge boundary used by the sampled FRI
  low-degree reduction.  The definitions are generic and are instantiated by
  the trace and composition FRI routes.
\<close>

context soundness
begin

definition generic_fri_sampled_query_restricted_bad_pairs
  :: "('f list \<Rightarrow> bool) \<Rightarrow> ('f list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow>
      (nat list \<times> 'f list) set"
where
  "generic_fri_sampled_query_restricted_bad_pairs low_degree candidate_bad
      degree_bound =
    generic_fri_sampled_query_bad_pair_union low_degree candidate_bad
      degree_bound \<inter> (fri_query_index_list_space \<times> UNIV)"

definition generic_fri_sampled_query_pair_fraction_bound
  :: "('f list \<Rightarrow> bool) \<Rightarrow> ('f list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow>
      prob \<Rightarrow> bool"
where
  "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
      degree_bound C \<longleftrightarrow>
    nnreal
      (card
        (generic_fri_sampled_query_restricted_bad_pairs low_degree
          candidate_bad degree_bound)) /
      nnreal
        (card fri_query_index_list_space *
          CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
    \<le> C"

definition generic_fri_sampled_query_challenge_projection
  :: "('f list \<Rightarrow> bool) \<Rightarrow> ('f list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow>
      'f list set"
where
  "generic_fri_sampled_query_challenge_projection low_degree candidate_bad
      degree_bound =
    snd `
      generic_fri_sampled_query_restricted_bad_pairs low_degree
        candidate_bad degree_bound"

definition generic_fri_sampled_query_query_fiber
  :: "('f list \<Rightarrow> bool) \<Rightarrow> ('f list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> nat list set"
where
  "generic_fri_sampled_query_query_fiber low_degree candidate_bad
      degree_bound challenges =
    fri_query_challenge_pair_query_fiber
      (generic_fri_sampled_query_restricted_bad_pairs low_degree
        candidate_bad degree_bound) challenges"

definition query_rounds_index_list_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "query_rounds_index_list_hit s query_idxs n out \<longleftrightarrow>
    (\<exists>results t raw_idxs.
      out = Some (results, t) \<and>
      length raw_idxs = n \<and>
      length query_idxs = n \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      (\<forall>i < n. \<exists>x.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i) x) =
          Some (raw_idxs ! i)))"

lemma card_fri_query_index_list_space:
  "card fri_query_index_list_space = card query_sample_space ^ rounds"
  unfolding fri_query_index_list_space_def
  using card_lists_length_eq[OF finite_query_sample_space, of rounds]
  by (simp add: conj_commute)

lemma query_rounds_index_list_hit_None[simp]:
  "\<not> query_rounds_index_list_hit s query_idxs n None"
  unfolding query_rounds_index_list_hit_def by simp

lemma query_rounds_index_list_hit_tail:
  assumes head:
      "Some ((), s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and tail:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s1)"
    and hit:
      "query_rounds_index_list_hit s query_idxs (Suc n)
        (Some (u # results, t))"
  shows
    "query_rounds_index_list_hit s1 (tl query_idxs) n
      (Some (results, t))"
proof -
  from hit obtain raw_idxs where
    len_raw: "length raw_idxs = Suc n"
    and len_query: "length query_idxs = Suc n"
    and query_eq: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookups:
      "\<And>i. i < Suc n \<Longrightarrow> \<exists>x.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i) x) =
          Some (raw_idxs ! i)"
    unfolding query_rounds_index_list_hit_def by auto
  have counter_s1: "PQueryCounter s1 = Suc (PQueryCounter s)"
    using verifier_query_round_program_outcome[OF head] by blast
  let ?raw_tail = "tl raw_idxs"
  have len_tail_raw: "length ?raw_tail = n"
    using len_raw by simp
  have len_tail_query: "length (tl query_idxs) = n"
    using len_query by simp
  have tail_eq:
    "tl query_idxs = map (\<lambda>raw. index (to_nat raw)) ?raw_tail"
    using query_eq by (cases raw_idxs; cases query_idxs; simp)
  have tail_lookups:
    "\<forall>i < n. \<exists>x.
      fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s1 + i) x) =
        Some (?raw_tail ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < n"
    then obtain x where lookup:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s + Suc i) x) =
        Some (raw_idxs ! Suc i)"
      using lookups[of "Suc i"] by auto
    have counter_eq: "PQueryCounter s1 + i = PQueryCounter s + Suc i"
      using counter_s1 by presburger
    have tail_raw: "?raw_tail ! i = raw_idxs ! Suc i"
      using i_bound len_raw by (cases raw_idxs) auto
    show "\<exists>x.
      fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s1 + i) x) =
        Some (?raw_tail ! i)"
      by (rule exI[where x=x])
        (use lookup counter_eq tail_raw in simp)
  qed
  show ?thesis
    unfolding query_rounds_index_list_hit_def
    by (intro exI[of _ results] exI[of _ t] exI[of _ ?raw_tail] conjI)
      (use len_tail_raw len_tail_query tail_eq tail_lookups in simp_all)
qed

lemma query_rounds_index_list_hit_head_index:
  assumes future: "query_future_fresh s"
    and head:
      "Some ((), s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and tail:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s1)"
    and hit:
      "query_rounds_index_list_hit s query_idxs (Suc n)
        (Some (u # results, t))"
  shows
    "query_round_any_index_set_hit s {query_idxs ! 0} (Some ((), s1))"
proof -
  from head[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    recv: "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    and after:
      "Some ((), s1) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final raw) s0)"
    by (auto elim!: set_dist_bindE)
  from hit obtain raw_idxs x where
    len_raw: "length raw_idxs = Suc n"
    and len_query: "length query_idxs = Suc n"
    and query_eq: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup_t:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) x) = Some (raw_idxs ! 0)"
    unfolding query_rounds_index_list_hit_def by auto
  have counter_s1: "PQueryCounter s1 = Suc (PQueryCounter s)"
    using verifier_query_round_program_outcome[OF head] by blast
  have past: "PQueryCounter s < PQueryCounter s1"
    using counter_s1 by simp
  have lookup_s1:
    "fmlookup (HashMap s1) (QueryIndexChallenge (PQueryCounter s) x) =
      Some (raw_idxs ! 0)"
    using ntimes_verifier_query_round_program_preserves_past_query_lookup
        [OF past tail, of x] lookup_t
    by simp
  have lookup_s0_x:
    "fmlookup (HashMap s0) (QueryIndexChallenge (PQueryCounter s) x) =
      Some (raw_idxs ! 0)"
    using verifier_query_round_after_index_program_preserves_query_lookup
        [OF after, of "PQueryCounter s" x] lookup_s1
    by simp
  have lookup_s0_current:
    "fmlookup (HashMap s0)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF recv] by blast
  have key_eq:
    "QueryIndexChallenge (PQueryCounter s) x =
      QueryIndexChallenge (PQueryCounter s) (PState s)"
  proof (rule ccontr)
    assume neq:
      "QueryIndexChallenge (PQueryCounter s) x \<noteq>
        QueryIndexChallenge (PQueryCounter s) (PState s)"
    have lookup_old:
      "fmlookup (HashMap s0) (QueryIndexChallenge (PQueryCounter s) x) =
        fmlookup (HashMap s) (QueryIndexChallenge (PQueryCounter s) x)"
      by (rule receive_query_index_challenge_preserves_other_lookup
          [OF recv neq])
    have "fmlookup (HashMap s) (QueryIndexChallenge (PQueryCounter s) x) =
        None"
      using future unfolding query_future_fresh_def by simp
    then show False
      using lookup_s0_x lookup_old by simp
  qed
  have raw_eq: "raw_idxs ! 0 = raw"
    using lookup_s0_x lookup_s0_current key_eq by simp
  have "index (to_nat raw) = query_idxs ! 0"
    using query_eq raw_eq len_raw by simp
  then show ?thesis
    unfolding query_round_any_index_set_hit_def
    using lookup_s1 raw_eq query_eq len_raw by auto
qed

lemma wp_ntimes_verifier_query_round_program_index_list_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and len_query: "length query_idxs = n"
    and subset: "set query_idxs \<subseteq> query_sample_space"
  shows
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n)
      (query_rounds_index_list_hit s query_idxs n) s \<le>
      (1 / nnreal (card query_sample_space)) ^ n"
  using future len_query subset
proof (induction n arbitrary: s query_idxs)
  case 0
  show ?case
    using wp_event_le_1
      [of "ntimes (verifier_query_round_program fr f_fl f_final as fl final) 0"
        "query_rounds_index_list_hit s query_idxs 0" s]
    by simp
next
  case (Suc n)
  let ?prog = "verifier_query_round_program fr f_fl f_final as fl final"
  let ?p = "1 / nnreal (card query_sample_space)"
  let ?Q = "query_rounds_index_list_hit s query_idxs (Suc n)"
  let ?Head = "query_round_any_index_set_hit s {query_idxs ! 0}"
  have query0_in: "query_idxs ! 0 \<in> query_sample_space"
    using Suc.prems(2,3) by (auto intro: nth_mem)
  have singleton_subset: "{query_idxs ! 0} \<subseteq> query_sample_space"
    using query0_in by simp
  have head_bound:
    "wp_event ?prog ?Head s \<le> ?p"
  proof -
    have base:
      "wp_event ?prog ?Head s \<le>
        nnreal (card {query_idxs ! 0}) /
          nnreal (card query_sample_space)"
      by (rule wp_verifier_query_round_program_any_index_set_bound
          [OF Suc.prems(1) raw_bound singleton_subset])
    then show ?thesis
      by simp
  qed
  show ?case
    unfolding ntimes.simps
  proof (rule order_trans)
    show
      "wp_event
        (?prog \<bind> (\<lambda>u. ntimes ?prog n \<bind> (\<lambda>xs. return (u # xs))))
        ?Q s
      \<le> wp_event ?prog ?Head s * (?p ^ n)"
    proof (rule wp_event_bind_bound_by_head_and_cont)
      show "\<not> ?Q None"
        by simp
    next
      fix u s1
      assume head:
        "Some (u, s1) \<in> set_dist (execute ?prog s)"
        and not_head: "\<not> ?Head (Some (u, s1))"
      have u_eq: "u = ()"
        by (cases u) simp
      show
        "wp_event
          (ntimes ?prog n \<bind> (\<lambda>xs. return (u # xs)))
          ?Q s1 = 0"
      proof (rule ccontr)
        assume nonzero:
          "wp_event
            (ntimes ?prog n \<bind> (\<lambda>xs. return (u # xs)))
            ?Q s1 \<noteq> 0"
        have positive:
          "0 <
            wp_event
              (ntimes ?prog n \<bind> (\<lambda>xs. return (u # xs)))
              ?Q s1"
          using nonzero by simp
        from wp_event_pos_imp_exists_support[OF positive]
        obtain out where out_support:
          "out \<in>
            set_dist
              (execute
                (ntimes ?prog n \<bind> (\<lambda>xs. return (u # xs))) s1)"
          and hit: "?Q out"
          by blast
        from hit obtain ys t0 raw_idxs where out_some: "out = Some (ys, t0)"
          unfolding query_rounds_index_list_hit_def by blast
        have "\<exists>results t.
          Some (results, t) \<in> set_dist (execute (ntimes ?prog n) s1) \<and>
          out = Some (u # results, t)"
        proof (rule set_dist_bindE[OF out_support[unfolded out_some]])
          fix results t
          assume tail:
            "Some (results, t) \<in> set_dist (execute (ntimes ?prog n) s1)"
            and ret:
            "Some (ys, t0) \<in> set_dist (execute (return (u # results)) t)"
          have out_eq: "out = Some (u # results, t)"
            using ret out_some
            unfolding set_dist_def return.rep_eq dist_return_def
              dist_delta_dist delta_map_def
            by simp
          show ?thesis
            using tail out_eq by blast
        qed
        then obtain results t where
          tail:
            "Some (results, t) \<in> set_dist (execute (ntimes ?prog n) s1)"
          and out_eq: "out = Some (u # results, t)"
          by blast
        have head_hit: "?Head (Some (u, s1))"
          unfolding u_eq
          by (rule query_rounds_index_list_hit_head_index
              [OF Suc.prems(1) head[unfolded u_eq] tail])
            (use hit out_eq u_eq in simp)
        then show False
          using not_head by simp
      qed
    next
      fix u s1
      assume head:
        "Some (u, s1) \<in> set_dist (execute ?prog s)"
        and head_hit: "?Head (Some (u, s1))"
      have u_eq: "u = ()"
        by (cases u) simp
      have future_s1: "query_future_fresh s1"
        by (rule verifier_query_round_program_preserves_query_future_fresh
            [OF Suc.prems(1) head[unfolded u_eq]])
      have tail_len: "length (tl query_idxs) = n"
        using Suc.prems(2) by simp
      have tail_subset: "set (tl query_idxs) \<subseteq> query_sample_space"
        using Suc.prems(3) by (cases query_idxs) auto
      have tail_bound:
        "wp_event (ntimes ?prog n)
          (query_rounds_index_list_hit s1 (tl query_idxs) n) s1 \<le>
          ?p ^ n"
        by (rule Suc.IH[OF future_s1 tail_len tail_subset])
      show
        "wp_event
          (ntimes ?prog n \<bind> (\<lambda>xs. return (u # xs)))
          ?Q s1 \<le> ?p ^ n"
      proof (rule order_trans[OF _ tail_bound])
        show
          "wp_event
            (ntimes ?prog n \<bind> (\<lambda>xs. return (u # xs)))
            ?Q s1
          \<le> wp_event (ntimes ?prog n)
            (query_rounds_index_list_hit s1 (tl query_idxs) n) s1"
        proof (rule wp_event_bind_bound_by_head_event)
          show
            "wp_event (ntimes ?prog n)
              (query_rounds_index_list_hit s1 (tl query_idxs) n) s1
            \<le> wp_event (ntimes ?prog n)
              (query_rounds_index_list_hit s1 (tl query_idxs) n) s1"
            by simp
        next
          show
            "?Q None \<Longrightarrow>
              query_rounds_index_list_hit s1 (tl query_idxs) n None"
            by simp
        next
          fix results t out
          assume tail:
            "Some (results, t) \<in> set_dist (execute (ntimes ?prog n) s1)"
            and ret:
            "out \<in> set_dist (execute (return (u # results)) t)"
            and hit: "?Q out"
          have out_eq: "out = Some (u # results, t)"
            using ret
            unfolding set_dist_def return.rep_eq dist_return_def
              dist_delta_dist delta_map_def
            by simp
          show "query_rounds_index_list_hit s1 (tl query_idxs) n
              (Some (results, t))"
            by (rule query_rounds_index_list_hit_tail
                [OF head[unfolded u_eq] tail])
              (use hit out_eq u_eq in simp)
        qed
      qed
    qed
  next
    show "wp_event ?prog ?Head s * ?p ^ n \<le> ?p ^ Suc n"
      using head_bound by (simp add: mult_right_mono)
  qed
qed

lemma wp_ntimes_verifier_query_round_program_index_list_set_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and finite_Q: "finite Q"
    and lengths: "\<And>query_idxs. query_idxs \<in> Q \<Longrightarrow> length query_idxs = n"
    and subsets:
      "\<And>query_idxs. query_idxs \<in> Q \<Longrightarrow>
        set query_idxs \<subseteq> query_sample_space"
  shows
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n)
      (\<lambda>out. \<exists>query_idxs \<in> Q.
        query_rounds_index_list_hit s query_idxs n out) s \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ n"
proof -
  have
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n)
      (\<lambda>out. \<exists>query_idxs \<in> Q.
        query_rounds_index_list_hit s query_idxs n out) s \<le>
      (\<Sum>query_idxs\<in>Q.
        (1 / nnreal (card query_sample_space)) ^ n)"
    by (rule wp_event_finite_UN_bound[OF finite_Q])
      (rule wp_ntimes_verifier_query_round_program_index_list_bound
        [OF future raw_bound lengths subsets])
  also have "... =
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ n"
    using finite_Q by simp
  finally show ?thesis .
qed

lemma wp_ntimes_verifier_query_round_program_fri_index_list_set_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event
      (ntimes
        (verifier_query_round_program fr f_fl f_final as fl final) rounds)
      (\<lambda>out. \<exists>query_idxs \<in> Q.
        query_rounds_index_list_hit s query_idxs rounds out) s \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
proof -
  have finite_Q: "finite Q"
    using subset by (rule finite_subset) (rule finite_fri_query_index_list_space)
  show ?thesis
  proof (rule wp_ntimes_verifier_query_round_program_index_list_set_bound
      [OF future raw_bound finite_Q])
    fix query_idxs
    assume "query_idxs \<in> Q"
    then show "length query_idxs = rounds"
      using subset unfolding fri_query_index_list_space_def by auto
  next
    fix query_idxs
    assume "query_idxs \<in> Q"
    then show "set query_idxs \<subseteq> query_sample_space"
      using subset unfolding fri_query_index_list_space_def by auto
  qed
qed

lemma generic_fri_sampled_query_query_fiber_entries_subset:
  "query_index_list_entries
      (generic_fri_sampled_query_query_fiber low_degree candidate_bad
        degree_bound challenges)
    \<subseteq> query_sample_space"
  unfolding query_index_list_entries_def
    generic_fri_sampled_query_query_fiber_def
    generic_fri_sampled_query_restricted_bad_pairs_def
    fri_query_challenge_pair_query_fiber_def
    fri_query_index_list_space_def
  by auto

lemma finite_generic_fri_sampled_query_query_fiber_entries:
  "finite
    (query_index_list_entries
      (generic_fri_sampled_query_query_fiber low_degree candidate_bad
        degree_bound challenges))"
  using generic_fri_sampled_query_query_fiber_entries_subset
  by (rule finite_subset) simp

lemma generic_fri_sampled_query_restricted_bad_pairs_subset:
  "generic_fri_sampled_query_restricted_bad_pairs low_degree candidate_bad
      degree_bound
    \<subseteq> fri_query_index_list_space \<times>
      fri_challenge_space
        (fri_round_count_for_degree_bound degree_bound)"
  unfolding generic_fri_sampled_query_restricted_bad_pairs_def
  using generic_fri_sampled_query_bad_pair_union_subset_challenge_space
    [of low_degree candidate_bad degree_bound]
  by blast

lemma finite_generic_fri_sampled_query_restricted_bad_pairs:
  "finite
    (generic_fri_sampled_query_restricted_bad_pairs low_degree candidate_bad
      degree_bound)"
proof (rule finite_subset)
  show
    "generic_fri_sampled_query_restricted_bad_pairs low_degree candidate_bad
      degree_bound
    \<subseteq> fri_query_index_list_space \<times>
      fri_challenge_space
        (fri_round_count_for_degree_bound degree_bound)"
    by (rule generic_fri_sampled_query_restricted_bad_pairs_subset)
  show
    "finite
      (fri_query_index_list_space \<times>
        fri_challenge_space
          (fri_round_count_for_degree_bound degree_bound))"
    by (simp add: finite_fri_query_index_list_space
        finite_fri_challenge_space)
qed

lemma generic_fri_sampled_query_pair_fraction_boundD:
  assumes
    "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
      degree_bound C"
  shows
    "nnreal
      (card
        (generic_fri_sampled_query_restricted_bad_pairs low_degree
          candidate_bad degree_bound)) /
      nnreal
        (card fri_query_index_list_space *
          CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
    \<le> C"
  using assms
  unfolding generic_fri_sampled_query_pair_fraction_bound_def .

lemma generic_fri_sampled_query_challenge_projection_subset:
  "generic_fri_sampled_query_challenge_projection low_degree candidate_bad
      degree_bound
    \<subseteq> fri_challenge_space
      (fri_round_count_for_degree_bound degree_bound)"
  unfolding generic_fri_sampled_query_challenge_projection_def
  using generic_fri_sampled_query_restricted_bad_pairs_subset
    [of low_degree candidate_bad degree_bound]
  by force

lemma generic_fri_sampled_query_query_fiber_subset:
  "generic_fri_sampled_query_query_fiber low_degree candidate_bad
      degree_bound challenges
    \<subseteq> fri_query_index_list_space"
  unfolding generic_fri_sampled_query_query_fiber_def
    generic_fri_sampled_query_restricted_bad_pairs_def
    fri_query_challenge_pair_query_fiber_def
  by auto

lemma finite_generic_fri_sampled_query_query_fiber:
  "finite
    (generic_fri_sampled_query_query_fiber low_degree candidate_bad
      degree_bound challenges)"
  using generic_fri_sampled_query_query_fiber_subset
    [of low_degree candidate_bad degree_bound challenges]
  by (rule finite_subset) (rule finite_fri_query_index_list_space)

lemma generic_fri_sampled_query_query_fiber_entries_card_le:
  "card
    (query_index_list_entries
      (generic_fri_sampled_query_query_fiber low_degree candidate_bad
        degree_bound challenges))
    \<le>
    card
      (generic_fri_sampled_query_query_fiber low_degree candidate_bad
        degree_bound challenges) * rounds"
  by (rule query_index_list_entries_card_le)
    (rule finite_generic_fri_sampled_query_query_fiber,
      rule generic_fri_sampled_query_query_fiber_subset)

lemma generic_fri_sampled_query_restricted_bad_pairs_as_fiber_Sigma:
  "generic_fri_sampled_query_restricted_bad_pairs low_degree candidate_bad
      degree_bound =
    (\<lambda>(challenges, query_idxs). (query_idxs, challenges)) `
      (SIGMA challenges:
        fri_challenge_space (fri_round_count_for_degree_bound degree_bound).
        generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges)"
  unfolding generic_fri_sampled_query_query_fiber_def
    fri_query_challenge_pair_query_fiber_def
  using generic_fri_sampled_query_restricted_bad_pairs_subset
  by force

lemma generic_fri_sampled_query_restricted_bad_pairs_card_eq_fiber_sum:
  "card
    (generic_fri_sampled_query_restricted_bad_pairs low_degree candidate_bad
      degree_bound) =
   (\<Sum>challenges \<in>
      fri_challenge_space (fri_round_count_for_degree_bound degree_bound).
      card
        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges))"
proof -
  let ?S =
    "SIGMA challenges:
      fri_challenge_space (fri_round_count_for_degree_bound degree_bound).
      generic_fri_sampled_query_query_fiber low_degree candidate_bad
        degree_bound challenges"
  let ?swap = "\<lambda>(challenges, query_idxs). (query_idxs, challenges)"
  have finite_S: "finite ?S"
    by (rule finite_SigmaI)
      (rule finite_fri_challenge_space,
       rule finite_generic_fri_sampled_query_query_fiber)
	  have inj: "inj_on ?swap ?S"
	    unfolding inj_on_def by auto
	  have finite_challenge_space:
	    "finite
	      (fri_challenge_space
	        (fri_round_count_for_degree_bound degree_bound))"
	    by (rule finite_fri_challenge_space)
	  have finite_fibers:
	    "\<And>challenges. challenges \<in>
	      fri_challenge_space (fri_round_count_for_degree_bound degree_bound)
	      \<Longrightarrow>
	      finite
	        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
	          degree_bound challenges)"
	    by (rule finite_generic_fri_sampled_query_query_fiber)
	  have card_S:
	    "card ?S =
	     (\<Sum>challenges \<in>
	      fri_challenge_space (fri_round_count_for_degree_bound degree_bound).
	      card
	        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
	          degree_bound challenges))"
	    by (rule card_SigmaI)
	      (use finite_challenge_space finite_fibers in auto)
	  have "card
	      (generic_fri_sampled_query_restricted_bad_pairs low_degree
	        candidate_bad degree_bound) =
	    card (?swap ` ?S)"
	    unfolding generic_fri_sampled_query_restricted_bad_pairs_as_fiber_Sigma
	    by simp
	  also have "... = card ?S"
	    by (rule card_image[OF inj])
	  also have "... =
	    (\<Sum>challenges \<in>
	      fri_challenge_space (fri_round_count_for_degree_bound degree_bound).
	      card
	        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
	          degree_bound challenges))"
	    by (rule card_S)
  finally show ?thesis .
qed

lemma generic_fri_sampled_query_pair_fraction_bound_from_fiber_sum:
  assumes fraction_bound:
    "nnreal
      (\<Sum>challenges \<in>
        fri_challenge_space (fri_round_count_for_degree_bound degree_bound).
        card
          (generic_fri_sampled_query_query_fiber low_degree candidate_bad
            degree_bound challenges)) /
      nnreal
        (card fri_query_index_list_space *
          CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
	  shows
	    "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
	      degree_bound C"
	proof -
	  have card_eq:
	    "card
	      (generic_fri_sampled_query_restricted_bad_pairs low_degree
	        candidate_bad degree_bound) =
	     (\<Sum>challenges \<in>
	      fri_challenge_space (fri_round_count_for_degree_bound degree_bound).
	      card
	        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
	          degree_bound challenges))"
	    by (rule generic_fri_sampled_query_restricted_bad_pairs_card_eq_fiber_sum)
	  show ?thesis
	    unfolding generic_fri_sampled_query_pair_fraction_bound_def
	    using fraction_bound card_eq by simp
	qed

lemma generic_fri_sampled_query_pair_fraction_bound_iff_fiber_sum:
  "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
      degree_bound C
    \<longleftrightarrow>
    nnreal
      (\<Sum>challenges \<in>
        fri_challenge_space (fri_round_count_for_degree_bound degree_bound).
        card
          (generic_fri_sampled_query_query_fiber low_degree candidate_bad
            degree_bound challenges)) /
      nnreal
        (card fri_query_index_list_space *
          CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
  unfolding generic_fri_sampled_query_pair_fraction_bound_def
  by (simp add:
      generic_fri_sampled_query_restricted_bad_pairs_card_eq_fiber_sum)

lemma trace_fri_sampled_query_restricted_bad_pairs_card_eq_fiber_sum:
  "card
    (trace_fri_sampled_query_bad_pair_union \<inter>
      (fri_query_index_list_space \<times> UNIV)) =
   (\<Sum>challenges \<in>
      fri_challenge_space (fri_round_count_for_degree_bound (clength - 1)).
      card
        (generic_fri_sampled_query_query_fiber trace_table_low_degree
          (Not \<circ> trace_table_low_degree) (clength - 1) challenges))"
proof -
  have generic:
    "card
      (generic_fri_sampled_query_restricted_bad_pairs trace_table_low_degree
        (Not \<circ> trace_table_low_degree) (clength - 1)) =
     (\<Sum>challenges \<in>
      fri_challenge_space (fri_round_count_for_degree_bound (clength - 1)).
      card
        (generic_fri_sampled_query_query_fiber trace_table_low_degree
          (Not \<circ> trace_table_low_degree) (clength - 1) challenges))"
    by (rule generic_fri_sampled_query_restricted_bad_pairs_card_eq_fiber_sum)
  then show ?thesis
    unfolding trace_fri_sampled_query_bad_pair_union_def
      generic_fri_sampled_query_restricted_bad_pairs_def
    by simp
qed

lemma composition_fri_sampled_query_restricted_bad_pairs_card_eq_fiber_sum:
  "card
    (composition_fri_sampled_query_bad_pair_union dg \<inter>
      (fri_query_index_list_space \<times> UNIV)) =
   (\<Sum>challenges \<in>
      fri_challenge_space (fri_round_count_for_degree_bound (to_nat dg)).
      card
        (generic_fri_sampled_query_query_fiber
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg)
          challenges))"
proof -
  have generic:
    "card
      (generic_fri_sampled_query_restricted_bad_pairs
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg)) =
     (\<Sum>challenges \<in>
      fri_challenge_space (fri_round_count_for_degree_bound (to_nat dg)).
      card
        (generic_fri_sampled_query_query_fiber
          (composition_table_low_degree (to_nat dg))
          (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg)
          challenges))"
    by (rule generic_fri_sampled_query_restricted_bad_pairs_card_eq_fiber_sum)
  then show ?thesis
    unfolding composition_fri_sampled_query_bad_pair_union_def
      generic_fri_sampled_query_restricted_bad_pairs_def
    by simp
qed

lemma trace_fri_sampled_query_pair_fraction_bound_iff_fiber_sum:
  "generic_fri_sampled_query_pair_fraction_bound trace_table_low_degree
      (Not \<circ> trace_table_low_degree) (clength - 1) C
    \<longleftrightarrow>
    nnreal
      (\<Sum>challenges \<in>
        fri_challenge_space (fri_round_count_for_degree_bound (clength - 1)).
        card
          (generic_fri_sampled_query_query_fiber trace_table_low_degree
            (Not \<circ> trace_table_low_degree) (clength - 1) challenges)) /
      nnreal
        (card fri_query_index_list_space *
          CARD('f) ^ fri_round_count_for_degree_bound (clength - 1))
      \<le> C"
  by (rule generic_fri_sampled_query_pair_fraction_bound_iff_fiber_sum)

lemma composition_fri_sampled_query_pair_fraction_bound_iff_fiber_sum:
  "generic_fri_sampled_query_pair_fraction_bound
      (composition_table_low_degree (to_nat dg))
      (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg) C
    \<longleftrightarrow>
    nnreal
      (\<Sum>challenges \<in>
        fri_challenge_space (fri_round_count_for_degree_bound (to_nat dg)).
        card
          (generic_fri_sampled_query_query_fiber
            (composition_table_low_degree (to_nat dg))
            (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg)
            challenges)) /
      nnreal
        (card fri_query_index_list_space *
          CARD('f) ^ fri_round_count_for_degree_bound (to_nat dg))
      \<le> C"
  by (rule generic_fri_sampled_query_pair_fraction_bound_iff_fiber_sum)

lemma trace_fri_query_index_list_set_hit_imp_query_rounds_any_index_set_hit:
  assumes hit: "trace_fri_query_index_list_set_hit s Q out"
  shows
    "query_rounds_any_index_set_hit s (query_index_list_entries Q) rounds
      out"
proof -
  from hit obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final query_idxs trace_round_layers
      composition_round_layers where
    openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        query_idxs trace_round_layers composition_round_layers"
    and query_in: "query_idxs \<in> Q"
    unfolding trace_fri_query_index_list_set_hit_def by blast
  from openings obtain result final_state query_start_state rest raw_idxs
      query_chunks trailing where
    out_eq: "out = Some (result, final_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks query_start_state query_chunks i)) =
          Some (raw_idxs ! i)"
    unfolding accepted_fri_opening_transcript_def
      verifier_query_indices_derived_def
    by blast
  have zero_bound: "0 < rounds"
    by (rule rounds_positive)
  have query_len: "length query_idxs = rounds"
    using query_idxs_eq len_raw by simp
  have idx_in_entries:
    "query_idxs ! 0 \<in> query_index_list_entries Q"
    using query_in zero_bound query_len
    unfolding query_index_list_entries_def
    by (auto intro: nth_mem)
  have idx_eq: "query_idxs ! 0 = index (to_nat (raw_idxs ! 0))"
    using query_idxs_eq len_raw zero_bound by simp
  show ?thesis
    unfolding query_rounds_any_index_set_hit_def
    apply (rule exI[where x=result])
    apply (rule exI[where x=final_state])
    apply (rule exI[where x=0])
    apply (rule exI[where x="state_after_query_chunks query_start_state
      query_chunks 0"])
    apply (rule exI[where x="raw_idxs ! 0"])
    using out_eq zero_bound lookup[OF zero_bound] idx_in_entries idx_eq
    by simp
qed

lemma composition_fri_query_index_list_set_hit_imp_query_rounds_any_index_set_hit:
  assumes hit: "composition_fri_query_index_list_set_hit s Q out"
  shows
    "query_rounds_any_index_set_hit s (query_index_list_entries Q) rounds
      out"
proof -
  from hit obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final query_idxs trace_round_layers
      composition_round_layers where
    openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        query_idxs trace_round_layers composition_round_layers"
    and query_in: "query_idxs \<in> Q"
    unfolding composition_fri_query_index_list_set_hit_def by blast
  from openings obtain result final_state query_start_state rest raw_idxs
      query_chunks trailing where
    out_eq: "out = Some (result, final_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks query_start_state query_chunks i)) =
          Some (raw_idxs ! i)"
    unfolding accepted_fri_opening_transcript_def
      verifier_query_indices_derived_def
    by blast
  have zero_bound: "0 < rounds"
    by (rule rounds_positive)
  have query_len: "length query_idxs = rounds"
    using query_idxs_eq len_raw by simp
  have idx_in_entries:
    "query_idxs ! 0 \<in> query_index_list_entries Q"
    using query_in zero_bound query_len
    unfolding query_index_list_entries_def
    by (auto intro: nth_mem)
  have idx_eq: "query_idxs ! 0 = index (to_nat (raw_idxs ! 0))"
    using query_idxs_eq len_raw zero_bound by simp
  show ?thesis
    unfolding query_rounds_any_index_set_hit_def
    apply (rule exI[where x=result])
    apply (rule exI[where x=final_state])
    apply (rule exI[where x=0])
    apply (rule exI[where x="state_after_query_chunks query_start_state
      query_chunks 0"])
    apply (rule exI[where x="raw_idxs ! 0"])
    using out_eq zero_bound lookup[OF zero_bound] idx_in_entries idx_eq
    by simp
qed

lemma wp_trace_fri_query_index_list_set_hit_bound_from_entries:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad (trace_fri_query_index_list_set_hit s Q) s \<le>
      nnreal rounds *
        (nnreal (card (query_index_list_entries Q)) /
          nnreal (card query_sample_space))"
proof -
  have event_bound:
    "wp_event verify_monad
      (query_rounds_any_index_set_hit s (query_index_list_entries Q) rounds)
      s \<le>
      nnreal rounds *
        (nnreal (card (query_index_list_entries Q)) /
          nnreal (card query_sample_space))"
    by (rule wp_verify_monad_query_rounds_any_index_set_bound
        [OF future raw_bound
          query_index_list_entries_subset_query_sample_space[OF subset]])
  show ?thesis
    by (rule order_trans[OF _ event_bound])
      (rule wp_event_mono,
        rule trace_fri_query_index_list_set_hit_imp_query_rounds_any_index_set_hit)
qed

lemma wp_composition_fri_query_index_list_set_hit_bound_from_entries:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad (composition_fri_query_index_list_set_hit s Q) s \<le>
      nnreal rounds *
        (nnreal (card (query_index_list_entries Q)) /
          nnreal (card query_sample_space))"
proof -
  have event_bound:
    "wp_event verify_monad
      (query_rounds_any_index_set_hit s (query_index_list_entries Q) rounds)
      s \<le>
      nnreal rounds *
        (nnreal (card (query_index_list_entries Q)) /
          nnreal (card query_sample_space))"
    by (rule wp_verify_monad_query_rounds_any_index_set_bound
        [OF future raw_bound
          query_index_list_entries_subset_query_sample_space[OF subset]])
  show ?thesis
    by (rule order_trans[OF _ event_bound])
      (rule wp_event_mono,
        rule composition_fri_query_index_list_set_hit_imp_query_rounds_any_index_set_hit)
qed

lemma generic_fri_sampled_query_pair_fraction_bound_mono:
  assumes
    "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
      degree_bound C"
    and "C \<le> D"
  shows
    "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
      degree_bound D"
  using assms
  unfolding generic_fri_sampled_query_pair_fraction_bound_def
  by (rule order_trans)

lemma generic_fri_sampled_query_pair_fraction_bound_from_card:
  assumes card_bound:
    "card
      (generic_fri_sampled_query_restricted_bad_pairs low_degree
        candidate_bad degree_bound) \<le> K"
    and fraction_bound:
    "nnreal K /
      nnreal
        (card fri_query_index_list_space *
          CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
  shows
    "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
      degree_bound C"
proof -
  have "nnreal
      (card
        (generic_fri_sampled_query_restricted_bad_pairs low_degree
          candidate_bad degree_bound)) /
      nnreal
        (card fri_query_index_list_space *
          CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
    \<le>
    nnreal K /
      nnreal
        (card fri_query_index_list_space *
          CARD('f) ^ fri_round_count_for_degree_bound degree_bound)"
    using card_bound by (rule nnreal_nat_divide_right_mono)
  also have "... \<le> C"
    by (rule fraction_bound)
  finally show ?thesis
    unfolding generic_fri_sampled_query_pair_fraction_bound_def .
qed

lemma generic_fri_sampled_query_restricted_bad_pairs_subset_Sigma:
  assumes projection:
    "generic_fri_sampled_query_challenge_projection low_degree candidate_bad
      degree_bound \<subseteq> B"
  shows
    "generic_fri_sampled_query_restricted_bad_pairs low_degree candidate_bad
      degree_bound
    \<subseteq>
    (\<lambda>(challenges, query_idxs). (query_idxs, challenges)) `
      (SIGMA challenges:B.
      generic_fri_sampled_query_query_fiber low_degree candidate_bad
        degree_bound challenges)"
proof
  fix pair
  assume pair_mem:
    "pair \<in>
      generic_fri_sampled_query_restricted_bad_pairs low_degree candidate_bad
        degree_bound"
  obtain query_idxs challenges where pair_eq: "pair = (query_idxs, challenges)"
    by (cases pair)
  have challenges_in: "challenges \<in> B"
    using projection pair_mem pair_eq
    unfolding generic_fri_sampled_query_challenge_projection_def
    by force
  have query_in:
    "query_idxs \<in>
      generic_fri_sampled_query_query_fiber low_degree candidate_bad
        degree_bound challenges"
    using pair_mem pair_eq
    unfolding generic_fri_sampled_query_query_fiber_def
      fri_query_challenge_pair_query_fiber_def
    by simp
  have "(challenges, query_idxs) \<in>
      (SIGMA challenges:B.
        generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges)"
    using challenges_in query_in by simp
  then show
    "pair \<in>
      (\<lambda>(challenges, query_idxs). (query_idxs, challenges)) `
        (SIGMA challenges:B.
          generic_fri_sampled_query_query_fiber low_degree candidate_bad
            degree_bound challenges)"
    using pair_eq by force
qed

lemma generic_fri_sampled_query_restricted_bad_pairs_card_le_from_fibers:
  assumes finite_B: "finite B"
    and projection:
      "generic_fri_sampled_query_challenge_projection low_degree
        candidate_bad degree_bound \<subseteq> B"
    and fiber_bound:
      "\<And>challenges. challenges \<in> B \<Longrightarrow>
        card
          (generic_fri_sampled_query_query_fiber low_degree candidate_bad
            degree_bound challenges) \<le> K"
  shows
    "card
      (generic_fri_sampled_query_restricted_bad_pairs low_degree
        candidate_bad degree_bound)
    \<le> card B * K"
proof -
  have subset:
    "generic_fri_sampled_query_restricted_bad_pairs low_degree candidate_bad
      degree_bound
    \<subseteq>
    (\<lambda>(challenges, query_idxs). (query_idxs, challenges)) `
      (SIGMA challenges:B.
      generic_fri_sampled_query_query_fiber low_degree candidate_bad
        degree_bound challenges)"
    by (rule generic_fri_sampled_query_restricted_bad_pairs_subset_Sigma
        [OF projection])
  have finite_fibers:
    "\<And>challenges. challenges \<in> B \<Longrightarrow>
      finite
        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges)"
    by (rule finite_generic_fri_sampled_query_query_fiber)
  have card_sigma:
    "card
      (SIGMA challenges:B.
        generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges)
      \<le> card B * K"
    using finite_B finite_fibers fiber_bound
  proof (induction rule: finite_induct)
    case empty
    then show ?case by simp
  next
    case (insert challenges B)
    have fiber_le:
      "card
        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges) \<le> K"
      by (rule insert.prems(2)) simp
    have tail_le:
      "card
        (SIGMA challenges:B.
          generic_fri_sampled_query_query_fiber low_degree candidate_bad
            degree_bound challenges)
        \<le> card B * K"
      by (rule insert.IH) (use insert.prems in auto)
    have "card
        (SIGMA challenges:insert challenges B.
          generic_fri_sampled_query_query_fiber low_degree candidate_bad
            degree_bound challenges)
      =
      card
        (generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges) +
      card
        (SIGMA challenges:B.
          generic_fri_sampled_query_query_fiber low_degree candidate_bad
            degree_bound challenges)"
      using insert.hyps insert.prems by simp
    also have "... \<le> K + card B * K"
      using fiber_le tail_le by simp
    also have "... = card (insert challenges B) * K"
      using insert.hyps by simp
    finally show ?case .
  qed
  have finite_sigma:
    "finite
      (SIGMA challenges:B.
        generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges)"
    by (rule finite_SigmaI[OF finite_B finite_fibers])
  then have finite_swap:
    "finite
      ((\<lambda>(challenges, query_idxs). (query_idxs, challenges)) `
        (SIGMA challenges:B.
          generic_fri_sampled_query_query_fiber low_degree candidate_bad
            degree_bound challenges))"
    by simp
  have "card
      (generic_fri_sampled_query_restricted_bad_pairs low_degree candidate_bad
        degree_bound)
    \<le>
    card
      ((\<lambda>(challenges, query_idxs). (query_idxs, challenges)) `
        (SIGMA challenges:B.
          generic_fri_sampled_query_query_fiber low_degree candidate_bad
            degree_bound challenges))"
    by (rule card_mono[OF finite_swap subset])
  also have "... \<le>
    card
      (SIGMA challenges:B.
        generic_fri_sampled_query_query_fiber low_degree candidate_bad
          degree_bound challenges)"
    by (rule card_image_le[OF finite_sigma])
  also have "... \<le> card B * K"
    by (rule card_sigma)
  finally show ?thesis .
qed

lemma generic_fri_sampled_query_pair_fraction_bound_from_projection_and_fibers:
  assumes finite_B: "finite B"
    and projection:
      "generic_fri_sampled_query_challenge_projection low_degree
        candidate_bad degree_bound \<subseteq> B"
    and fiber_bound:
      "\<And>challenges. challenges \<in> B \<Longrightarrow>
        card
          (generic_fri_sampled_query_query_fiber low_degree candidate_bad
            degree_bound challenges) \<le> K"
    and fraction_bound:
      "nnreal (card B * K) /
        nnreal
          (card fri_query_index_list_space *
            CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
        \<le> C"
  shows
    "generic_fri_sampled_query_pair_fraction_bound low_degree candidate_bad
      degree_bound C"
proof (rule generic_fri_sampled_query_pair_fraction_bound_from_card)
  show
    "card
      (generic_fri_sampled_query_restricted_bad_pairs low_degree
        candidate_bad degree_bound)
    \<le> card B * K"
    by (rule generic_fri_sampled_query_restricted_bad_pairs_card_le_from_fibers
        [OF finite_B projection fiber_bound])
  show
    "nnreal (card B * K) /
      nnreal
        (card fri_query_index_list_space *
          CARD('f) ^ fri_round_count_for_degree_bound degree_bound)
      \<le> C"
    by (rule fraction_bound)
qed

end

end
