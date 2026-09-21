theory Soundness_FRI_Conditioned_Actual_Bridge
  imports
    Soundness_FRI_Conditioned_RO_Security
    Soundness_FRI_Conditioned_Authenticated_Bridge
    Soundness_FRI_Conditioned_Query_Fiber
    Soundness_FRI_RO_Actual_Query_Joint_Evidence
begin

context soundness
begin

lemma ro_verify_monad_with_fri_prefixes_outcome_projection:
  assumes outcome:
    "Some ((fri_prefixes, result), final_state) \<in>
      set_dist
        (execute ro_verify_monad_with_fri_prefixes initial)"
  shows
    "Some (result, final_state) \<in>
      set_dist (execute ro_verify_monad initial)"
proof -
  have projected:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ro_verify_monad_with_fri_prefixes \<bind>
              (\<lambda>x. return (snd x)))
            initial)"
    by (rule set_dist_bindI[OF outcome]) simp
  show ?thesis
    using projected
    unfolding ro_verify_monad_with_fri_prefixes_projection .
qed

lemma ro_receive_trace_fri_commits_with_prefix_outcome_extensions:
  assumes outcome:
    "Some (((before, root_state), (b, fri_root)), after) \<in>
      set_dist
        (execute ro_receive_trace_fri_commits_with_prefix initial)"
  shows "before = initial \<and> initial \<le> root_state \<and> root_state \<le> after"
proof -
  from outcome obtain absorb_state challenge_state where
    absorb_out:
      "Some (fri_root, absorb_state) \<in>
        set_dist (execute protocol_absorb_read initial)"
    and root_eq: "root_state = absorb_state"
    and challenge_out:
      "Some (b, challenge_state) \<in>
        set_dist (execute receive_trace_fri_challenge absorb_state)"
    and after_eq: "after = challenge_state"
    and before_eq: "before = initial"
    unfolding ro_receive_trace_fri_commits_with_prefix_def
    by (auto elim!: set_dist_bindE)
  have initial_root: "initial \<le> root_state"
    unfolding root_eq
    by (rule hash_target_program_outcome_extension[
        OF hash_target_program_protocol_absorb_read absorb_out])
  have root_after: "root_state \<le> after"
    unfolding root_eq after_eq
    by (rule hash_target_program_outcome_extension[
        OF hash_target_program_receive_trace_fri_challenge challenge_out])
  show ?thesis
    using before_eq initial_root root_after by simp
qed

lemma ro_receive_composition_fri_commits_with_prefix_outcome_extensions:
  assumes outcome:
    "Some (((before, root_state), (b, fri_root)), after) \<in>
      set_dist
        (execute ro_receive_composition_fri_commits_with_prefix initial)"
  shows "before = initial \<and> initial \<le> root_state \<and> root_state \<le> after"
proof -
  from outcome obtain absorb_state challenge_state where
    absorb_out:
      "Some (fri_root, absorb_state) \<in>
        set_dist (execute protocol_absorb_read initial)"
    and root_eq: "root_state = absorb_state"
    and challenge_out:
      "Some (b, challenge_state) \<in>
        set_dist (execute receive_composition_fri_challenge absorb_state)"
    and after_eq: "after = challenge_state"
    and before_eq: "before = initial"
    unfolding ro_receive_composition_fri_commits_with_prefix_def
    by (auto elim!: set_dist_bindE)
  have initial_root: "initial \<le> root_state"
    unfolding root_eq
    by (rule hash_target_program_outcome_extension[
        OF hash_target_program_protocol_absorb_read absorb_out])
  have root_after: "root_state \<le> after"
    unfolding root_eq after_eq
    by (rule hash_target_program_outcome_extension[
        OF hash_target_program_receive_composition_fri_challenge challenge_out])
  show ?thesis
    using before_eq initial_root root_after by simp
qed

lemma ntimes_ro_receive_trace_fri_commits_with_prefix_extensions:
  assumes outcome:
    "Some (fri_fri_items, final_state) \<in>
      set_dist
        (execute (ntimes ro_receive_trace_fri_commits_with_prefix n)
          initial)"
  shows
    "initial \<le> final_state \<and>
      (\<forall>fri_item \<in> set fri_fri_items.
        (case fri_item of ((_, root_state), _) \<Rightarrow> root_state \<le> final_state))"
  using outcome
proof (induction n arbitrary: initial fri_fri_items final_state)
  case 0
  then show ?case by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain fri_item middle tail_fri_fri_items where
    head_out:
      "Some (fri_item, middle) \<in>
        set_dist
          (execute ro_receive_trace_fri_commits_with_prefix initial)"
    and tail_out:
      "Some (tail_fri_fri_items, final_state) \<in>
        set_dist
          (execute (ntimes ro_receive_trace_fri_commits_with_prefix n)
            middle)"
    and fri_fri_items_eq: "fri_fri_items = fri_item # tail_fri_fri_items"
    by (auto elim!: set_dist_bindE)
  have step_ext:
      "fst (fst fri_item) = initial \<and>
        initial \<le> snd (fst fri_item) \<and> snd (fst fri_item) \<le> middle"
    by (rule ro_receive_trace_fri_commits_with_prefix_outcome_extensions[
        where before="fst (fst fri_item)"
          and root_state="snd (fst fri_item)"
          and b="fst (snd fri_item)"
          and fri_root="snd (snd fri_item)"])
      (use head_out in simp)
  have tail_ext:
      "middle \<le> final_state \<and>
        (\<forall>x \<in> set tail_fri_fri_items.
          (case x of ((_, s), _) \<Rightarrow> s \<le> final_state))"
    by (rule Suc.IH[OF tail_out])
  have initial_final: "initial \<le> final_state"
    using step_ext tail_ext by (meson hash_ext_trans)
  have root_final: "snd (fst fri_item) \<le> final_state"
    using step_ext tail_ext by (meson hash_ext_trans)
  show ?case
    unfolding fri_fri_items_eq
    using initial_final root_final tail_ext
    by (cases fri_item; case_tac a) simp
qed

lemma ntimes_ro_receive_composition_fri_commits_with_prefix_extensions:
  assumes outcome:
    "Some (fri_items, final_state) \<in>
      set_dist
        (execute (ntimes ro_receive_composition_fri_commits_with_prefix n)
          initial)"
  shows
    "initial \<le> final_state \<and>
      (\<forall>fri_item \<in> set fri_items.
        (case fri_item of ((_, root_state), _) \<Rightarrow> root_state \<le> final_state))"
  using outcome
proof (induction n arbitrary: initial fri_items final_state)
  case 0
  then show ?case by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain fri_item middle tail_items where
    head_out:
      "Some (fri_item, middle) \<in>
        set_dist
          (execute ro_receive_composition_fri_commits_with_prefix initial)"
    and tail_out:
      "Some (tail_items, final_state) \<in>
        set_dist
          (execute (ntimes ro_receive_composition_fri_commits_with_prefix n)
            middle)"
    and items_eq: "fri_items = fri_item # tail_items"
    by (auto elim!: set_dist_bindE)
  have step_ext:
      "fst (fst fri_item) = initial \<and>
        initial \<le> snd (fst fri_item) \<and> snd (fst fri_item) \<le> middle"
    by (rule ro_receive_composition_fri_commits_with_prefix_outcome_extensions[
        where before="fst (fst fri_item)"
          and root_state="snd (fst fri_item)"
          and b="fst (snd fri_item)"
          and fri_root="snd (snd fri_item)"])
      (use head_out in simp)
  have tail_ext:
      "middle \<le> final_state \<and>
        (\<forall>x \<in> set tail_items.
          (case x of ((_, s), _) \<Rightarrow> s \<le> final_state))"
    by (rule Suc.IH[OF tail_out])
  have initial_final: "initial \<le> final_state"
    using step_ext tail_ext by (meson hash_ext_trans)
  have root_final: "snd (fst fri_item) \<le> final_state"
    using step_ext tail_ext by (meson hash_ext_trans)
  show ?case
    unfolding items_eq
    using initial_final root_final tail_ext
    by (cases fri_item; case_tac a) simp
qed

lemma hash_extension_preserving_of_projection:
  fixes m :: "('x, 'f protocol_channel) state_monad"
    and n :: "('y, 'f protocol_channel) state_monad"
  assumes projection: "m \<bind> (\<lambda>x. return (project x)) = n"
    and extension: "hash_extension_preserving n"
  shows "hash_extension_preserving m"
  unfolding hash_extension_preserving_def
proof (intro allI impI)
  fix s x t
  assume out: "Some (x, t) \<in> set_dist (execute m s)"
  have projected:
      "Some (project x, t) \<in>
        set_dist (execute (m \<bind> (\<lambda>x. return (project x))) s)"
    by (rule set_dist_bindI[OF out]) simp
  have projected_n:
      "Some (project x, t) \<in> set_dist (execute n s)"
    using projected unfolding projection .
  show "s \<le> t"
    using extension projected_n
    unfolding hash_extension_preserving_def by blast
qed

lemma hash_extension_preserving_ro_verify_after_trace_commits:
  "hash_extension_preserving
    (ro_verify_after_trace_commits fr trace_commits f_final as)"
  unfolding ro_verify_after_trace_commits_def
  apply (rule hash_extension_preserving_bind)
   apply (rule hash_target_program_extension)
   apply (rule hash_target_program_protocol_absorb_read)
  apply (rule hash_extension_preserving_bind)
   apply (rule hash_target_program_extension)
   apply (rule hash_target_program_assert)
  apply (rule hash_extension_preserving_bind)
   apply (rule hash_target_program_extension)
   apply (rule hash_target_program_ntimes)
   apply (rule hash_target_program_ro_receive_composition_fri_commits)
  apply (rule hash_extension_preserving_bind)
   apply (rule hash_target_program_extension)
   apply (rule hash_target_program_protocol_absorb_read)
  apply (rule hash_target_program_extension)
  apply (rule hash_target_program_ntimes)
  apply (rule hash_target_program_ro_verifier_query_round_program_exact)
  done

lemma hash_extension_preserving_ro_verify_after_trace_commits_with_fri_prefixes:
  "hash_extension_preserving
    (ro_verify_after_trace_commits_with_fri_prefixes
      fr trace_commits f_final as)"
  by (rule hash_extension_preserving_of_projection[
      OF ro_verify_after_trace_commits_with_fri_prefixes_projection
        hash_extension_preserving_ro_verify_after_trace_commits])

lemma ro_verify_monad_with_fri_prefixes_trace_root_states_extend:
  assumes outcome:
    "Some ((((trace_items, dg, composition_items), result)), final_state) \<in>
      set_dist
        (execute ro_verify_monad_with_fri_prefixes initial)"
  shows
    "\<forall>fri_item \<in> set trace_items.
      (case fri_item of ((_, root_state), _) \<Rightarrow> root_state \<le> final_state)"
proof -
  from outcome obtain fr after_fr after_trace f_final after_final as after_alpha
      tail_result after_tail where
    trace_out:
      "Some (trace_items, after_trace) \<in>
        set_dist
          (execute
            (ntimes ro_receive_trace_fri_commits_with_prefix
              (ceil_log clength))
            after_fr)"
    and final_out:
      "Some (f_final, after_final) \<in>
        set_dist (execute protocol_absorb_read after_trace)"
    and alpha_out:
      "Some (as, after_alpha) \<in>
        set_dist
          (execute (mmap (replicate (length spec) ro_alpha_round))
            after_final)"
    and tail_out:
      "Some (tail_result, after_tail) \<in>
        set_dist
          (execute
            (ro_verify_after_trace_commits_with_fri_prefixes
              fr (map snd trace_items) f_final as)
            after_alpha)"
    and final_eq: "final_state = after_tail"
    unfolding ro_verify_monad_with_fri_prefixes_def
    by (auto elim!: set_dist_bindE)
  have trace_ext:
      "after_fr \<le> after_trace \<and>
        (\<forall>fri_item \<in> set trace_items.
          (case fri_item of ((_, root_state), _) \<Rightarrow>
            root_state \<le> after_trace))"
    by (rule ntimes_ro_receive_trace_fri_commits_with_prefix_extensions[
        OF trace_out])
  have after_trace_final: "after_trace \<le> final_state"
  proof -
    have e1: "after_trace \<le> after_final"
      by (rule hash_target_program_outcome_extension[
          OF hash_target_program_protocol_absorb_read final_out])
    have alpha_program:
        "hash_target_program B (length spec * (1 + 1))
          (mmap (replicate (length spec) ro_alpha_round))"
    proof -
      have each:
          "\<And>m. m \<in> set (replicate (length spec) ro_alpha_round) \<Longrightarrow>
            hash_target_program B (1 + 1) m"
      proof -
        fix m
        assume "m \<in> set (replicate (length spec) ro_alpha_round)"
        then have "m = ro_alpha_round" by simp
        then show "hash_target_program B (1 + 1) m"
          by (simp only: add_Suc_right add_0
              hash_target_program_ro_alpha_round)
      qed
      have
          "hash_target_program B
            (length (replicate (length spec) ro_alpha_round) * (1 + 1))
            (mmap (replicate (length spec) ro_alpha_round))"
        by (rule hash_target_program_mmap[OF each])
      then show ?thesis by simp
    qed
    have e2: "after_final \<le> after_alpha"
      by (rule hash_target_program_outcome_extension[OF alpha_program alpha_out])
    have e3: "after_alpha \<le> after_tail"
      using hash_extension_preserving_ro_verify_after_trace_commits_with_fri_prefixes
        tail_out
      unfolding hash_extension_preserving_def by blast
    show ?thesis
      unfolding final_eq
      using e1 e2 e3 by (meson hash_ext_trans)
  qed
  show ?thesis
  proof (intro ballI)
    fix fri_item
    assume in_items: "fri_item \<in> set trace_items"
    have root_trace:
        "(case fri_item of ((_, root_state), _) \<Rightarrow>
          root_state \<le> after_trace)"
      using trace_ext in_items by blast
    show
        "(case fri_item of ((_, root_state), _) \<Rightarrow>
          root_state \<le> final_state)"
      using root_trace after_trace_final
      by (cases fri_item; case_tac a) (auto intro: hash_ext_trans)
  qed
qed

lemma ro_verify_after_trace_commits_with_fri_prefixes_composition_root_states_extend:
  assumes outcome:
    "Some (((dg, composition_items), result), final_state) \<in>
      set_dist
        (execute
          (ro_verify_after_trace_commits_with_fri_prefixes
            fr trace_commits f_final as)
          initial)"
  shows
    "to_nat dg \<le> maxDegree \<and>
      (\<forall>fri_item \<in> set composition_items.
        (case fri_item of ((_, root_state), _) \<Rightarrow>
          root_state \<le> final_state))"
proof -
  from outcome obtain after_dg after_assert after_composition final after_final
      after_queries where
    assert_out:
      "Some ((), after_assert) \<in>
        set_dist
          (execute (assert (to_nat dg \<le> maxDegree)) after_dg)"
    and composition_out:
      "Some (composition_items, after_composition) \<in>
        set_dist
          (execute
            (ntimes ro_receive_composition_fri_commits_with_prefix
              (ceil_log (to_nat dg + 1)))
            after_assert)"
    and final_out:
      "Some (final, after_final) \<in>
        set_dist (execute protocol_absorb_read after_composition)"
    and query_out:
      "Some (result, after_queries) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program fr trace_commits f_final as
                (map snd composition_items) final)
              rounds)
            after_final)"
    and final_eq: "final_state = after_queries"
    unfolding ro_verify_after_trace_commits_with_fri_prefixes_def
    by (auto elim!: set_dist_bindE)
  have degree_bound: "to_nat dg \<le> maxDegree"
    using assert_out
    unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
  have composition_ext:
      "after_assert \<le> after_composition \<and>
        (\<forall>fri_item \<in> set composition_items.
          (case fri_item of ((_, root_state), _) \<Rightarrow>
            root_state \<le> after_composition))"
    by (rule
        ntimes_ro_receive_composition_fri_commits_with_prefix_extensions[
          OF composition_out])
  have after_composition_final: "after_composition \<le> final_state"
  proof -
    have e1: "after_composition \<le> after_final"
      by (rule hash_target_program_outcome_extension[
          OF hash_target_program_protocol_absorb_read final_out])
    have query_program:
        "hash_target_program B
          (rounds *
            (1 + ro_verifier_query_decommit_hash_budget +
              (length trace_commits + length (map snd composition_items)) *
                ro_verifier_fri_layer_hash_budget))
          (ntimes
            (ro_verifier_query_round_program fr trace_commits f_final as
              (map snd composition_items) final)
            rounds)"
      by (rule hash_target_program_ntimes)
        (rule hash_target_program_ro_verifier_query_round_program_exact)
    have e2: "after_final \<le> after_queries"
      by (rule hash_target_program_outcome_extension[
          OF query_program query_out])
    show ?thesis
      unfolding final_eq
      by (rule hash_ext_trans[OF e1 e2])
  qed
  have roots_final:
      "\<forall>fri_item \<in> set composition_items.
        (case fri_item of ((_, root_state), _) \<Rightarrow>
          root_state \<le> final_state)"
  proof (intro ballI)
    fix fri_item
    assume in_items: "fri_item \<in> set composition_items"
    have root_composition:
        "(case fri_item of ((_, root_state), _) \<Rightarrow>
          root_state \<le> after_composition)"
      using composition_ext in_items by blast
    show
        "(case fri_item of ((_, root_state), _) \<Rightarrow>
          root_state \<le> final_state)"
      using root_composition after_composition_final
      by (cases fri_item; case_tac a) (auto intro: hash_ext_trans)
  qed
  show ?thesis
    using degree_bound roots_final by simp
qed

lemma ro_verify_monad_with_fri_prefixes_all_root_states_extend:
  assumes outcome:
    "Some ((((trace_items, dg, composition_items), result)), final_state) \<in>
      set_dist
        (execute ro_verify_monad_with_fri_prefixes initial)"
  shows
    "(\<forall>fri_item \<in> set trace_items.
        (case fri_item of ((_, root_state), _) \<Rightarrow>
          root_state \<le> final_state)) \<and>
      to_nat dg \<le> maxDegree \<and>
      (\<forall>fri_item \<in> set composition_items.
        (case fri_item of ((_, root_state), _) \<Rightarrow>
          root_state \<le> final_state))"
proof -
  have trace:
      "\<forall>fri_item \<in> set trace_items.
        (case fri_item of ((_, root_state), _) \<Rightarrow>
          root_state \<le> final_state)"
    by (rule ro_verify_monad_with_fri_prefixes_trace_root_states_extend[
        OF outcome])
  from outcome obtain fr f_final as after_alpha where
    tail_out:
      "Some (((dg, composition_items), result), final_state) \<in>
        set_dist
          (execute
            (ro_verify_after_trace_commits_with_fri_prefixes
              fr (map snd trace_items) f_final as)
            after_alpha)"
    unfolding ro_verify_monad_with_fri_prefixes_def
    by (auto elim!: set_dist_bindE)
  have composition:
      "to_nat dg \<le> maxDegree \<and>
        (\<forall>fri_item \<in> set composition_items.
          (case fri_item of ((_, root_state), _) \<Rightarrow>
            root_state \<le> final_state))"
    by (rule
        ro_verify_after_trace_commits_with_fri_prefixes_composition_root_states_extend[
          OF tail_out])
  show ?thesis
    using trace composition by simp
qed

definition fri_ro_prefix_root_state
  :: "'f fri_ro_prefix_item \<Rightarrow> 'f protocol_channel"
where
  "fri_ro_prefix_root_state fri_item = snd (fst fri_item)"

definition fri_ro_prefix_challenge :: "'f fri_ro_prefix_item \<Rightarrow> 'f"
where
  "fri_ro_prefix_challenge fri_item = fst (snd fri_item)"

definition fri_ro_prefix_root :: "'f fri_ro_prefix_item \<Rightarrow> 'f"
where
  "fri_ro_prefix_root fri_item = snd (snd fri_item)"

definition fri_ro_prefix_roots :: "'f fri_ro_prefix_item list \<Rightarrow> 'f list"
where
  "fri_ro_prefix_roots fri_items = map fri_ro_prefix_root fri_items"

definition fri_ro_prefix_challenges :: "'f fri_ro_prefix_item list \<Rightarrow> 'f list"
where
  "fri_ro_prefix_challenges fri_items = map fri_ro_prefix_challenge fri_items"

definition fri_ro_prefix_conceptual_layers
  :: "'f fri_ro_prefix_item list \<Rightarrow> 'f \<Rightarrow> 'f list list"
where
  "fri_ro_prefix_conceptual_layers fri_items final_value =
    map
      (\<lambda>j. conceptual_table
        (fri_ro_prefix_root_state (fri_items ! j))
        (fri_ro_prefix_root (fri_items ! j))
        (length (fri_canonical_domain_at j)))
      [0..<length fri_items] @
    [replicate (length (fri_canonical_domain_at (length fri_items)))
      final_value]"

definition fri_ro_prefix_merkle_target_hit
  :: "'f fri_ro_prefix_item list \<Rightarrow> 'f protocol_channel \<Rightarrow> bool"
where
  "fri_ro_prefix_merkle_target_hit fri_items final_state \<longleftrightarrow>
    (\<exists>j < length fri_items.
      hash_map_new_output_hit
        (merkle_prefix_path_targets
          {fri_ro_prefix_root (fri_items ! j)}
          (fri_ro_prefix_root_state (fri_items ! j)))
        (fri_ro_prefix_root_state (fri_items ! j)) final_state)"

lemma fri_ro_prefix_conceptual_layers_at:
  assumes j_bound: "j < length fri_items"
  shows
    "fri_ro_prefix_conceptual_layers fri_items final_value ! j =
      conceptual_table
        (fri_ro_prefix_root_state (fri_items ! j))
        (fri_ro_prefix_root (fri_items ! j))
        (length (fri_canonical_domain_at j))"
  unfolding fri_ro_prefix_conceptual_layers_def
  by (simp add: nth_append j_bound)

lemma fri_ro_prefix_conceptual_layers_final:
  "fri_ro_prefix_conceptual_layers fri_items final_value !
      length fri_items =
    replicate (length (fri_canonical_domain_at (length fri_items)))
      final_value"
  unfolding fri_ro_prefix_conceptual_layers_def
  by (simp add: nth_append)

lemma ro_verify_monad_with_fri_prefixes_indexed_extensions:
  assumes outcome:
    "Some ((((trace_items, dg, composition_items), result)), final_state) \<in>
      set_dist
        (execute ro_verify_monad_with_fri_prefixes initial)"
  shows
    "(\<forall>j < length trace_items.
        fri_ro_prefix_root_state (trace_items ! j) \<le> final_state) \<and>
      to_nat dg \<le> maxDegree \<and>
      (\<forall>j < length composition_items.
        fri_ro_prefix_root_state (composition_items ! j) \<le> final_state)"
proof -
  have all:
      "(\<forall>fri_item \<in> set trace_items.
          (case fri_item of ((_, root_state), _) \<Rightarrow>
            root_state \<le> final_state)) \<and>
        to_nat dg \<le> maxDegree \<and>
        (\<forall>fri_item \<in> set composition_items.
          (case fri_item of ((_, root_state), _) \<Rightarrow>
            root_state \<le> final_state))"
    by (rule ro_verify_monad_with_fri_prefixes_all_root_states_extend[
        OF outcome])
  have trace_indexed:
      "\<forall>j < length trace_items.
        fri_ro_prefix_root_state (trace_items ! j) \<le> final_state"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length trace_items"
    have in_items: "trace_items ! j \<in> set trace_items"
      by (rule nth_mem[OF j_bound])
    have root_le:
        "(case trace_items ! j of ((_, root_state), _) \<Rightarrow>
          root_state \<le> final_state)"
      using all in_items by simp
    show
        "fri_ro_prefix_root_state (trace_items ! j) \<le> final_state"
      using root_le
      unfolding fri_ro_prefix_root_state_def
      by (cases "trace_items ! j"; case_tac a) simp
  qed
  have composition_indexed:
      "\<forall>j < length composition_items.
        fri_ro_prefix_root_state (composition_items ! j) \<le> final_state"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length composition_items"
    have in_items: "composition_items ! j \<in> set composition_items"
      by (rule nth_mem[OF j_bound])
    have root_le:
        "(case composition_items ! j of ((_, root_state), _) \<Rightarrow>
          root_state \<le> final_state)"
      using all in_items by simp
    show
        "fri_ro_prefix_root_state (composition_items ! j) \<le> final_state"
      using root_le
      unfolding fri_ro_prefix_root_state_def
      by (cases "composition_items ! j"; case_tac a) simp
  qed
  show ?thesis
    using all trace_indexed composition_indexed by simp
qed

lemma fri_ro_prefix_states_clean_if_final_clean:
  assumes extensions:
      "\<And>j. j < length fri_items \<Longrightarrow>
        fri_ro_prefix_root_state (fri_items ! j) \<le> final_state"
    and final_clean: "\<not> hash_map_output_collision final_state"
  shows
    "\<And>j. j < length fri_items \<Longrightarrow>
      \<not> hash_map_output_collision
        (fri_ro_prefix_root_state (fri_items ! j))"
proof -
  fix j
  assume j_bound: "j < length fri_items"
  show
      "\<not> hash_map_output_collision
        (fri_ro_prefix_root_state (fri_items ! j))"
  proof
    assume collision:
        "hash_map_output_collision
          (fri_ro_prefix_root_state (fri_items ! j))"
    have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[
          OF collision extensions[OF j_bound]])
    then show False
      using final_clean by contradiction
  qed
qed

lemma fri_ro_prefix_no_targetD:
  assumes no_target:
      "\<not> fri_ro_prefix_merkle_target_hit fri_items final_state"
    and j_bound: "j < length fri_items"
  shows
    "\<not> hash_map_new_output_hit
      (merkle_prefix_path_targets
        {fri_ro_prefix_root (fri_items ! j)}
        (fri_ro_prefix_root_state (fri_items ! j)))
      (fri_ro_prefix_root_state (fri_items ! j)) final_state"
  using no_target j_bound
  unfolding fri_ro_prefix_merkle_target_hit_def by blast

lemma fri_ro_authenticated_chain_conditioned_split:
  assumes chain:
      "generic_fri_recorded_value_chain_evidence
        (fri_ro_prefix_roots fri_items)
        (fri_ro_prefix_challenges fri_items) final_value
        query_idxs round_layers"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count: "length fri_items = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and extensions:
      "\<And>j. j < length fri_items \<Longrightarrow>
        fri_ro_prefix_root_state (fri_items ! j) \<le> final_state"
    and final_clean: "\<not> hash_map_output_collision final_state"
    and no_target:
      "\<not> fri_ro_prefix_merkle_target_hit fri_items final_state"
    and authenticated:
      "generic_fri_recorded_chunks_authenticated
        (fri_ro_prefix_roots fri_items) query_idxs round_layers final_state"
    and start_not_low:
      "\<not> fri_table_low_degree_on (fri_padded_degree_bound d)
        (fri_canonical_domain_at 0)
        (fri_conditioned_layer_table 0
          (fri_ro_prefix_conceptual_layers fri_items final_value ! 0))"
  shows
    "fri_ro_prefix_challenges fri_items \<in>
        generic_fri_bad_challenge_lists (length fri_items)
          (fri_conditioned_bad_challenges d
            (\<lambda>j _. fri_ro_prefix_conceptual_layers fri_items final_value ! j)) \<or>
      (\<exists>i < length fri_items.
        query_idxs \<in>
          fri_conditioned_residual_query_lists
            (fri_ro_prefix_roots fri_items)
            (fri_ro_prefix_challenges fri_items)
            (fri_ro_prefix_conceptual_layers fri_items final_value) i)"
proof -
  let ?roots = "fri_ro_prefix_roots fri_items"
  let ?challenges = "fri_ro_prefix_challenges fri_items"
  let ?layers = "fri_ro_prefix_conceptual_layers fri_items final_value"
  let ?prefix_state =
    "\<lambda>j. fri_ro_prefix_root_state (fri_items ! j)"
  have challenge_len: "length ?challenges = length fri_items"
    unfolding fri_ro_prefix_challenges_def by simp
  have roots_len: "length ?roots = length fri_items"
    unfolding fri_ro_prefix_roots_def by simp
  have prefix_ext:
      "\<And>j. j < length ?challenges \<Longrightarrow> ?prefix_state j \<le> final_state"
    unfolding challenge_len
    by (rule extensions)
  have prefix_clean:
      "\<And>j. j < length ?challenges \<Longrightarrow>
        \<not> hash_map_output_collision (?prefix_state j)"
    unfolding challenge_len
    by (rule fri_ro_prefix_states_clean_if_final_clean[
        OF extensions final_clean])
  have no_prefix_target:
      "\<And>j. j < length ?challenges \<Longrightarrow>
        \<not> hash_map_new_output_hit
          (merkle_prefix_path_targets {?roots ! j} (?prefix_state j))
          (?prefix_state j) final_state"
  proof -
    fix j
    assume j_bound: "j < length ?challenges"
    have item_bound: "j < length fri_items"
      using j_bound challenge_len by simp
    have root_at:
        "?roots ! j = fri_ro_prefix_root (fri_items ! j)"
      unfolding fri_ro_prefix_roots_def
      using item_bound by simp
    show
        "\<not> hash_map_new_output_hit
          (merkle_prefix_path_targets {?roots ! j} (?prefix_state j))
          (?prefix_state j) final_state"
      unfolding root_at
      by (rule fri_ro_prefix_no_targetD[OF no_target item_bound])
  qed
  have recorded_authenticated:
      "\<And>round_idx j.
        round_idx < length query_idxs \<Longrightarrow>
        j < length ?challenges \<Longrightarrow>
        generic_fri_recorded_layer_chunk_authenticated ?roots query_idxs
          round_layers final_state round_idx j"
    using authenticated challenge_len roots_len
    unfolding generic_fri_recorded_chunks_authenticated_def
      generic_fri_recorded_layer_chunk_authenticated_def
    by simp
  have layer_at:
      "\<And>j. j < length ?challenges \<Longrightarrow>
        ?layers ! j = conceptual_table (?prefix_state j) (?roots ! j)
          (length (fri_canonical_domain_at j))"
  proof -
    fix j
    assume j_bound: "j < length ?challenges"
    have item_bound: "j < length fri_items"
      using j_bound challenge_len by simp
    show
        "?layers ! j = conceptual_table (?prefix_state j) (?roots ! j)
          (length (fri_canonical_domain_at j))"
      unfolding fri_ro_prefix_conceptual_layers_at[OF item_bound]
        fri_ro_prefix_roots_def
      using item_bound by simp
  qed
  have final_layer:
      "?layers ! length ?challenges =
        replicate (length (fri_canonical_domain_at (length ?challenges)))
          final_value"
    unfolding challenge_len
    by (rule fri_ro_prefix_conceptual_layers_final)
  have split:
      "?challenges \<in>
          generic_fri_bad_challenge_lists (length ?challenges)
            (fri_conditioned_bad_challenges d (\<lambda>j _. ?layers ! j)) \<or>
        (\<exists>i < length ?challenges.
          query_idxs \<in>
            fri_conditioned_residual_query_lists ?roots ?challenges
              ?layers i)"
    apply (rule authenticated_recorded_chain_conditioned_split[
        where N=N and d=d, OF chain eval_power _ rounds_le prefix_ext prefix_clean
          no_prefix_target recorded_authenticated layer_at final_layer
          start_not_low])
    using round_count challenge_len
    by simp
  show ?thesis
    using split challenge_len by simp
qed

lemma fri_ro_verifier_outcome_authenticated_chain_conditioned_split:
  assumes verifier_out:
      "Some ((((trace_items, dg, composition_items), result)), final_state) \<in>
        set_dist
          (execute ro_verify_monad_with_fri_prefixes initial)"
    and side:
      "fri_items = trace_items \<or> fri_items = composition_items"
    and chain:
      "generic_fri_recorded_value_chain_evidence
        (fri_ro_prefix_roots fri_items)
        (fri_ro_prefix_challenges fri_items) final_value
        query_idxs round_layers"
    and eval_power: "clength * scale = 2 ^ N"
    and round_count: "length fri_items = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and final_clean: "\<not> hash_map_output_collision final_state"
    and no_target:
      "\<not> fri_ro_prefix_merkle_target_hit fri_items final_state"
    and authenticated:
      "generic_fri_recorded_chunks_authenticated
        (fri_ro_prefix_roots fri_items) query_idxs round_layers final_state"
    and start_not_low:
      "\<not> fri_table_low_degree_on (fri_padded_degree_bound d)
        (fri_canonical_domain_at 0)
        (fri_conditioned_layer_table 0
          (fri_ro_prefix_conceptual_layers fri_items final_value ! 0))"
  shows
    "to_nat dg \<le> maxDegree \<and>
      (fri_ro_prefix_challenges fri_items \<in>
          generic_fri_bad_challenge_lists (length fri_items)
            (fri_conditioned_bad_challenges d
              (\<lambda>j _. fri_ro_prefix_conceptual_layers fri_items final_value ! j)) \<or>
        (\<exists>i < length fri_items.
          query_idxs \<in>
            fri_conditioned_residual_query_lists
              (fri_ro_prefix_roots fri_items)
              (fri_ro_prefix_challenges fri_items)
              (fri_ro_prefix_conceptual_layers fri_items final_value) i))"
proof -
  have indexed:
      "(\<forall>j < length trace_items.
          fri_ro_prefix_root_state (trace_items ! j) \<le> final_state) \<and>
        to_nat dg \<le> maxDegree \<and>
        (\<forall>j < length composition_items.
          fri_ro_prefix_root_state (composition_items ! j) \<le> final_state)"
    by (rule ro_verify_monad_with_fri_prefixes_indexed_extensions[
        OF verifier_out])
  have degree_bound: "to_nat dg \<le> maxDegree"
    using indexed by simp
  have extensions:
      "\<And>j. j < length fri_items \<Longrightarrow>
        fri_ro_prefix_root_state (fri_items ! j) \<le> final_state"
    using indexed side by blast
  have split:
      "fri_ro_prefix_challenges fri_items \<in>
          generic_fri_bad_challenge_lists (length fri_items)
            (fri_conditioned_bad_challenges d
              (\<lambda>j _. fri_ro_prefix_conceptual_layers fri_items final_value ! j)) \<or>
        (\<exists>i < length fri_items.
          query_idxs \<in>
            fri_conditioned_residual_query_lists
              (fri_ro_prefix_roots fri_items)
              (fri_ro_prefix_challenges fri_items)
              (fri_ro_prefix_conceptual_layers fri_items final_value) i)"
    by (rule fri_ro_authenticated_chain_conditioned_split[
        OF chain eval_power round_count rounds_le extensions final_clean
          no_target authenticated start_not_low])
  show ?thesis
    using degree_bound split by simp
qed

end
end