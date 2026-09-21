theory Staged_Security_Experiment_RO_Verifier_Budgets
  imports Staged_Security_Experiment_RO_Checked
begin

context soundness
begin

lemma ro_receive_query_commits_eq_fri_layer_opening_steps:
  "ro_receive_query_commits fl = map ro_fri_layer_opening_step fl"
  unfolding ro_receive_query_commits_def by simp

lemma hash_target_program_ro_fri_layer_opening_steps_mfold_state:
  fixes st :: "nat \<times> 'f \<times> nat \<times> nat"
  assumes init:
    "case st of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
  shows
    "hash_target_program B
      (length fl * (2 * (Suc L + Suc L)))
      (mfold st (map ro_fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
  using init
proof (induction fl arbitrary: st)
  case Nil
  then show ?case
    by (simp add: hash_target_program_return)
next
  case (Cons bf fl)
  obtain i x len pw where st_eq: "st = (i, x, len, pw)"
    by (cases st)
  obtain b f where bf_eq: "bf = (b, f)"
    by (cases bf)
  let ?N = "2 * (Suc L + Suc L)"
  have len_le: "floor_log len \<le> L"
    using Cons.prems unfolding st_eq by simp
  have head:
    "hash_target_program B ?N
      (ro_fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    unfolding bf_eq st_eq
    by (rule hash_target_program_ro_fri_layer_opening_step[OF len_le])
  have tail:
    "hash_target_program B (length fl * ?N)
      (mfold z (map ro_fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    if out:
      "Some (z, t) \<in>
        set_dist (execute (ro_fri_layer_opening_step bf st) s)"
    for z and s :: "'f protocol_channel"
      and t :: "'f protocol_channel"
  proof -
    have z_inv:
      "case z of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
      unfolding bf_eq st_eq
      by (rule ro_fri_layer_opening_step_preserves_floor_log_bound[OF len_le out[unfolded bf_eq st_eq]])
    show ?thesis
      by (rule Cons.IH[OF z_inv])
  qed
  have "hash_target_program B (?N + length fl * ?N)
      ((ro_fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>z. mfold z (map ro_fri_layer_opening_step fl)))"
    by (rule hash_target_program_bind_on_outcomes[OF head]) (rule tail)
  then show ?case
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma hash_target_program_ro_receive_query_commits_mfold:
  assumes init: "floor_log len \<le> L"
  shows
    "hash_target_program B
      (length fl * (2 * (Suc L + Suc L)))
      (mfold (i, x, len, pw) (ro_receive_query_commits fl))"
  unfolding ro_receive_query_commits_eq_fri_layer_opening_steps
proof -
  have st_inv:
    "case (i, x, len, pw) of
      (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
    using init by simp
  show "hash_target_program B (length fl * (2 * (Suc L + Suc L)))
    (mfold (i, x, len, pw) (map ro_fri_layer_opening_step fl) ::
      (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    by (rule hash_target_program_ro_fri_layer_opening_steps_mfold_state
        [OF st_inv])
qed

lemma hash_range_budget_ro_fri_layer_opening_steps_mfold_state:
  fixes st :: "nat \<times> 'f \<times> nat \<times> nat"
  assumes init:
    "case st of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
  shows
    "hash_range_budget
      (length fl * (2 * (Suc L + Suc L)))
      (mfold st (map ro_fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
  using init
proof (induction fl arbitrary: st)
  case Nil
  then show ?case
    by (simp add: hash_range_budget_return)
next
  case (Cons bf fl)
  obtain i x len pw where st_eq: "st = (i, x, len, pw)"
    by (cases st)
  obtain b f where bf_eq: "bf = (b, f)"
    by (cases bf)
  let ?B = "2 * (Suc L + Suc L)"
  have len_le: "floor_log len \<le> L"
    using Cons.prems unfolding st_eq by simp
  have head:
    "hash_range_budget ?B
      (ro_fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    unfolding bf_eq st_eq
    by (rule hash_range_budget_ro_fri_layer_opening_step[OF len_le])
  have tail:
    "hash_range_budget (length fl * ?B)
      (mfold z (map ro_fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    if out:
      "Some (z, t) \<in>
        set_dist (execute (ro_fri_layer_opening_step bf st) s)"
    for z and s :: "'f protocol_channel"
      and t :: "'f protocol_channel"
  proof -
    have z_inv:
      "case z of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
      unfolding bf_eq st_eq
      by (rule ro_fri_layer_opening_step_preserves_floor_log_bound[OF len_le out[unfolded bf_eq st_eq]])
    show ?thesis
      by (rule Cons.IH[OF z_inv])
  qed
  have "hash_range_budget (?B + length fl * ?B)
      ((ro_fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>z. mfold z (map ro_fri_layer_opening_step fl)))"
    by (rule hash_range_budget_bind_on_outcomes[OF head]) (rule tail)
  then show ?case
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma hash_range_budget_ro_receive_query_commits_mfold:
  assumes init: "floor_log len \<le> L"
  shows
    "hash_range_budget
      (length fl * (2 * (Suc L + Suc L)))
      (mfold (i, x, len, pw) (ro_receive_query_commits fl))"
  unfolding ro_receive_query_commits_eq_fri_layer_opening_steps
proof -
  have st_inv:
    "case (i, x, len, pw) of
      (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
    using init by simp
  show "hash_range_budget (length fl * (2 * (Suc L + Suc L)))
    (mfold (i, x, len, pw) (map ro_fri_layer_opening_step fl) ::
      (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    by (rule hash_range_budget_ro_fri_layer_opening_steps_mfold_state
        [OF st_inv])
qed

lemma hash_collision_budget_ro_fri_layer_opening_steps_mfold_state:
  fixes st :: "nat \<times> 'f \<times> nat \<times> nat"
  assumes init:
    "case st of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
  shows
    "hash_collision_budget
      (length fl * (2 * (Suc L + Suc L)))
      (mfold st (map ro_fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
  using init
proof (induction fl arbitrary: st)
  case Nil
  then show ?case
    by (simp add: hash_collision_budget_return)
next
  case (Cons bf fl)
  obtain i x len pw where st_eq: "st = (i, x, len, pw)"
    by (cases st)
  obtain b f where bf_eq: "bf = (b, f)"
    by (cases bf)
  let ?B = "2 * (Suc L + Suc L)"
  have len_le: "floor_log len \<le> L"
    using Cons.prems unfolding st_eq by simp
  have head_range:
    "hash_range_budget ?B
      (ro_fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    unfolding bf_eq st_eq
    by (rule hash_range_budget_ro_fri_layer_opening_step[OF len_le])
  have head_collision:
    "hash_collision_budget ?B
      (ro_fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    unfolding bf_eq st_eq
    by (rule hash_collision_budget_ro_fri_layer_opening_step[OF len_le])
  have tail_range:
    "hash_range_budget (length fl * ?B)
      (mfold z (map ro_fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    if out:
      "Some (z, t) \<in>
        set_dist (execute (ro_fri_layer_opening_step bf st) s)"
    for z and s :: "'f protocol_channel"
      and t :: "'f protocol_channel"
  proof -
    have z_inv:
      "case z of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
      unfolding bf_eq st_eq
      by (rule ro_fri_layer_opening_step_preserves_floor_log_bound[OF len_le out[unfolded bf_eq st_eq]])
    show ?thesis
      by (rule hash_range_budget_ro_fri_layer_opening_steps_mfold_state
          [OF z_inv])
  qed
  have tail_collision:
    "hash_collision_budget (length fl * ?B)
      (mfold z (map ro_fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    if out:
      "Some (z, t) \<in>
        set_dist (execute (ro_fri_layer_opening_step bf st) s)"
    for z and s :: "'f protocol_channel"
      and t :: "'f protocol_channel"
  proof -
    have z_inv:
      "case z of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
      unfolding bf_eq st_eq
      by (rule ro_fri_layer_opening_step_preserves_floor_log_bound[OF len_le out[unfolded bf_eq st_eq]])
    show ?thesis
      by (rule Cons.IH[OF z_inv])
  qed
  have "hash_collision_budget (?B + length fl * ?B)
      ((ro_fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>z. mfold z (map ro_fri_layer_opening_step fl)))"
    by (rule hash_collision_budget_bind_on_outcomes
        [OF head_range head_collision tail_range tail_collision])
  then show ?case
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma hash_collision_budget_ro_receive_query_commits_mfold:
  assumes init: "floor_log len \<le> L"
  shows
    "hash_collision_budget
      (length fl * (2 * (Suc L + Suc L)))
      (mfold (i, x, len, pw) (ro_receive_query_commits fl))"
  unfolding ro_receive_query_commits_eq_fri_layer_opening_steps
proof -
  have st_inv:
    "case (i, x, len, pw) of
      (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
    using init by simp
  show "hash_collision_budget (length fl * (2 * (Suc L + Suc L)))
    (mfold (i, x, len, pw) (map ro_fri_layer_opening_step fl) ::
      (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    by (rule hash_collision_budget_ro_fri_layer_opening_steps_mfold_state
        [OF st_inv])
qed

lemma hash_target_program_ro_verifier_query_round_program_exact:
  "hash_target_program B
    (1 + ro_verifier_query_decommit_hash_budget +
      (length f_fl + length fl) * ro_verifier_fri_layer_hash_budget)
    (ro_verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?L = "floor_log (clength * scale)"
  let ?B = "ro_verifier_fri_layer_hash_budget"
  have B_eq: "?B = 2 * (Suc ?L + Suc ?L)"
    unfolding ro_verifier_fri_layer_hash_budget_def
      verifier_fri_layer_hash_budget_def by simp
  have after_comp:
    "hash_target_program B (length fl * ?B + 0)
      ((mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (ro_receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))"
    for idx fv
  proof (rule hash_target_program_bind)
    show "hash_target_program B (length fl * ?B)
      (mfold
        (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
        (ro_receive_query_commits fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule hash_target_program_ro_receive_query_commits_mfold) simp
    show "\<And>x. hash_target_program B 0
      ((case x of (i, x, len, pw) \<Rightarrow> assert (x = final)) ::
        (unit, 'f protocol_channel) state_monad)"
      by (simp add: hash_target_program_assert split: prod.splits)
  qed
  have after_trace:
    "hash_target_program B
      (length f_fl * ?B + (0 + (length fl * ?B + 0)))
      ((mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
          'f protocol_channel) state_monad) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pow).
          assert (f_x = f_final) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final)))))"
    for idx fv
  proof (rule hash_target_program_bind)
    show "hash_target_program B (length f_fl * ?B)
      (mfold (idx, hd fv, clength * scale, 1)
        (ro_receive_query_commits f_fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule hash_target_program_ro_receive_query_commits_mfold) simp
    fix x :: "nat \<times> 'f \<times> nat \<times> nat"
    obtain f_i f_x f_len f_pow where x_eq:
      "x = (f_i, f_x, f_len, f_pow)"
      by (cases x) auto
    have case_budget:
      "hash_target_program B (0 + (length fl * ?B + 0))
        ((assert (f_x = f_final) ::
          (unit, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))"
      by (rule hash_target_program_bind
          [OF hash_target_program_assert after_comp])
    show "hash_target_program B (0 + (length fl * ?B + 0))
      ((case x of (f_i, f_x, f_len, f_pow) \<Rightarrow>
        assert (f_x = f_final) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (ro_receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final)))) ::
        (unit, 'f protocol_channel) state_monad)"
      using case_budget
      unfolding x_eq
      by (simp split: prod.splits)
  qed
  have after_query:
    "hash_target_program B
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + (0 + (length fl * ?B + 0))))
      (mmap (ro_check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (ro_receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                'f protocol_channel) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    by (rule hash_target_program_bind)
      (rule hash_target_program_ro_check_decommit_on_query, rule after_trace)
  have after_query_simple:
    "hash_target_program B
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      (mmap (ro_check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (ro_receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                'f protocol_channel) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    using after_query[of idx] by simp
  have after_random:
    "hash_target_program B
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      ((let idx' = index (to_nat idx) in
          mmap (ro_check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (ro_receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  'f protocol_channel) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    for idx
    using after_query_simple[of "index (to_nat idx)"]
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
  have "hash_target_program B
      (1 + (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B)))
      (receive_query_index_challenge \<bind>
        (\<lambda>idx.
          let idx' = index (to_nat idx) in
          mmap (ro_check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (ro_receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  'f protocol_channel) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    by (rule hash_target_program_bind
        [OF hash_target_program_receive_query_index_challenge])
      (rule after_random)
  then show ?thesis
    unfolding ro_verifier_query_round_program_def
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
qed

lemma hash_range_budget_ro_verifier_query_round_program_exact:
  "hash_range_budget
    (1 + ro_verifier_query_decommit_hash_budget +
      (length f_fl + length fl) * ro_verifier_fri_layer_hash_budget)
    (ro_verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?L = "floor_log (clength * scale)"
  let ?B = "ro_verifier_fri_layer_hash_budget"
  have B_eq: "?B = 2 * (Suc ?L + Suc ?L)"
    unfolding ro_verifier_fri_layer_hash_budget_def
      verifier_fri_layer_hash_budget_def by simp
  have after_comp:
    "hash_range_budget (length fl * ?B + 0)
      ((mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (ro_receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))"
    for idx fv
  proof (rule hash_range_budget_bind)
    show "hash_range_budget (length fl * ?B)
      (mfold
        (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
        (ro_receive_query_commits fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule hash_range_budget_ro_receive_query_commits_mfold) simp
    show "\<And>x. hash_range_budget 0
      ((case x of (i, x, len, pw) \<Rightarrow> assert (x = final)) ::
        (unit, 'f protocol_channel) state_monad)"
      by (simp add: hash_range_budget_assert split: prod.splits)
  qed
  have after_trace:
    "hash_range_budget
      (length f_fl * ?B + (0 + (length fl * ?B + 0)))
      ((mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
          'f protocol_channel) state_monad) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pow).
          assert (f_x = f_final) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final)))))"
    for idx fv
  proof (rule hash_range_budget_bind)
    show "hash_range_budget (length f_fl * ?B)
      (mfold (idx, hd fv, clength * scale, 1)
        (ro_receive_query_commits f_fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule hash_range_budget_ro_receive_query_commits_mfold) simp
    fix x :: "nat \<times> 'f \<times> nat \<times> nat"
    obtain f_i f_x f_len f_pow where x_eq:
      "x = (f_i, f_x, f_len, f_pow)"
      by (cases x) auto
    have case_budget:
      "hash_range_budget (0 + (length fl * ?B + 0))
        ((assert (f_x = f_final) ::
          (unit, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))"
      by (rule hash_range_budget_bind
          [OF hash_range_budget_assert after_comp])
    show "hash_range_budget (0 + (length fl * ?B + 0))
      ((case x of (f_i, f_x, f_len, f_pow) \<Rightarrow>
        assert (f_x = f_final) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (ro_receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final)))) ::
        (unit, 'f protocol_channel) state_monad)"
      using case_budget
      unfolding x_eq
      by (simp split: prod.splits)
  qed
  have after_query:
    "hash_range_budget
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + (0 + (length fl * ?B + 0))))
      (mmap (ro_check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (ro_receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                'f protocol_channel) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_check_decommit_on_query, rule after_trace)
  have after_query_simple:
    "hash_range_budget
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      (mmap (ro_check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (ro_receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                'f protocol_channel) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    using after_query[of idx] by simp
  have after_random:
    "hash_range_budget
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      ((let idx' = index (to_nat idx) in
          mmap (ro_check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (ro_receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  'f protocol_channel) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    for idx
    using after_query_simple[of "index (to_nat idx)"]
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
  have "hash_range_budget
      (1 + (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B)))
      (receive_query_index_challenge \<bind>
        (\<lambda>idx.
          let idx' = index (to_nat idx) in
          mmap (ro_check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (ro_receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  'f protocol_channel) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    by (rule hash_range_budget_bind
        [OF hash_range_budget_receive_query_index_challenge])
      (rule after_random)
  then show ?thesis
    unfolding ro_verifier_query_round_program_def
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
qed

lemma hash_collision_budget_ro_verifier_query_round_program_exact:
  "hash_collision_budget
    (1 + ro_verifier_query_decommit_hash_budget +
      (length f_fl + length fl) * ro_verifier_fri_layer_hash_budget)
    (ro_verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?L = "floor_log (clength * scale)"
  let ?B = "ro_verifier_fri_layer_hash_budget"
  have B_eq: "?B = 2 * (Suc ?L + Suc ?L)"
    unfolding ro_verifier_fri_layer_hash_budget_def
      verifier_fri_layer_hash_budget_def by simp
  have after_comp_range:
    "hash_range_budget (length fl * ?B + 0)
      ((mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (ro_receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))"
    for idx fv
  proof (rule hash_range_budget_bind)
    show "hash_range_budget (length fl * ?B)
      (mfold
        (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
        (ro_receive_query_commits fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule hash_range_budget_ro_receive_query_commits_mfold) simp
    show "\<And>x. hash_range_budget 0
      ((case x of (i, x, len, pw) \<Rightarrow> assert (x = final)) ::
        (unit, 'f protocol_channel) state_monad)"
      by (simp add: hash_range_budget_assert split: prod.splits)
  qed
  have after_comp_collision:
    "hash_collision_budget (length fl * ?B + 0)
      ((mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (ro_receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))"
    for idx fv
  proof (rule hash_collision_budget_bind)
    show "hash_range_budget (length fl * ?B)
      (mfold
        (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
        (ro_receive_query_commits fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule hash_range_budget_ro_receive_query_commits_mfold) simp
    show "hash_collision_budget (length fl * ?B)
      (mfold
        (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
        (ro_receive_query_commits fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule hash_collision_budget_ro_receive_query_commits_mfold) simp
    show "\<And>x. hash_range_budget 0
      ((case x of (i, x, len, pw) \<Rightarrow> assert (x = final)) ::
        (unit, 'f protocol_channel) state_monad)"
      by (simp add: hash_range_budget_assert split: prod.splits)
    show "\<And>x. hash_collision_budget 0
      ((case x of (i, x, len, pw) \<Rightarrow> assert (x = final)) ::
        (unit, 'f protocol_channel) state_monad)"
      by (simp add: hash_collision_budget_assert split: prod.splits)
  qed
  have after_trace_range:
    "hash_range_budget
      (length f_fl * ?B + (0 + (length fl * ?B + 0)))
      ((mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
          'f protocol_channel) state_monad) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pow).
          assert (f_x = f_final) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final)))))"
    for idx fv
  proof (rule hash_range_budget_bind)
    show "hash_range_budget (length f_fl * ?B)
      (mfold (idx, hd fv, clength * scale, 1)
        (ro_receive_query_commits f_fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule hash_range_budget_ro_receive_query_commits_mfold) simp
    fix x :: "nat \<times> 'f \<times> nat \<times> nat"
    obtain f_i f_x f_len f_pow where x_eq:
      "x = (f_i, f_x, f_len, f_pow)"
      by (cases x) auto
    have case_budget:
      "hash_range_budget (0 + (length fl * ?B + 0))
        ((assert (f_x = f_final) ::
          (unit, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))"
      by (rule hash_range_budget_bind
          [OF hash_range_budget_assert after_comp_range])
    show "hash_range_budget (0 + (length fl * ?B + 0))
      ((case x of (f_i, f_x, f_len, f_pow) \<Rightarrow>
        assert (f_x = f_final) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (ro_receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final)))) ::
        (unit, 'f protocol_channel) state_monad)"
      using case_budget unfolding x_eq by (simp split: prod.splits)
  qed
  have after_trace_collision:
    "hash_collision_budget
      (length f_fl * ?B + (0 + (length fl * ?B + 0)))
      ((mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
          'f protocol_channel) state_monad) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pow).
          assert (f_x = f_final) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final)))))"
    for idx fv
  proof (rule hash_collision_budget_bind)
    show "hash_range_budget (length f_fl * ?B)
      (mfold (idx, hd fv, clength * scale, 1)
        (ro_receive_query_commits f_fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule hash_range_budget_ro_receive_query_commits_mfold) simp
    show "hash_collision_budget (length f_fl * ?B)
      (mfold (idx, hd fv, clength * scale, 1)
        (ro_receive_query_commits f_fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule hash_collision_budget_ro_receive_query_commits_mfold) simp
    fix x :: "nat \<times> 'f \<times> nat \<times> nat"
    obtain f_i f_x f_len f_pow where x_eq:
      "x = (f_i, f_x, f_len, f_pow)"
      by (cases x) auto
    have case_range:
      "hash_range_budget (0 + (length fl * ?B + 0))
        ((assert (f_x = f_final) ::
          (unit, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))"
      by (rule hash_range_budget_bind
          [OF hash_range_budget_assert after_comp_range])
    have case_collision:
      "hash_collision_budget (0 + (length fl * ?B + 0))
        ((assert (f_x = f_final) ::
          (unit, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))"
      by (rule hash_collision_budget_bind
          [OF hash_range_budget_assert hash_collision_budget_assert
              after_comp_range after_comp_collision])
    show "hash_range_budget (0 + (length fl * ?B + 0))
      ((case x of (f_i, f_x, f_len, f_pow) \<Rightarrow>
        assert (f_x = f_final) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (ro_receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final)))) ::
        (unit, 'f protocol_channel) state_monad)"
      using case_range unfolding x_eq by (simp split: prod.splits)
    show "hash_collision_budget (0 + (length fl * ?B + 0))
      ((case x of (f_i, f_x, f_len, f_pow) \<Rightarrow>
        assert (f_x = f_final) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (ro_receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final)))) ::
        (unit, 'f protocol_channel) state_monad)"
      using case_collision unfolding x_eq by (simp split: prod.splits)
  qed
  have after_query_range:
    "hash_range_budget
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + (0 + (length fl * ?B + 0))))
      (mmap (ro_check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (ro_receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                'f protocol_channel) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_check_decommit_on_query, rule after_trace_range)
  have after_query_collision:
    "hash_collision_budget
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + (0 + (length fl * ?B + 0))))
      (mmap (ro_check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (ro_receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                'f protocol_channel) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
  proof (rule hash_collision_budget_bind)
    show "hash_range_budget ro_verifier_query_decommit_hash_budget
      (mmap (ro_check_decommit_on_query fr idx))"
      by (rule hash_range_budget_ro_check_decommit_on_query)
    show "hash_collision_budget ro_verifier_query_decommit_hash_budget
      (mmap (ro_check_decommit_on_query fr idx))"
      by (rule hash_collision_budget_ro_check_decommit_on_query)
    show "\<And>fv. hash_range_budget
      (length f_fl * ?B + (0 + (length fl * ?B + 0)))
      ((mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pow).
          assert (f_x = f_final) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final)))))"
      by (rule after_trace_range)
    show "\<And>fv. hash_collision_budget
      (length f_fl * ?B + (0 + (length fl * ?B + 0)))
      ((mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pow).
          assert (f_x = f_final) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final)))))"
      by (rule after_trace_collision)
  qed
  have after_query_range_simple:
    "hash_range_budget
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      (mmap (ro_check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (ro_receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                'f protocol_channel) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    using after_query_range[of idx] by simp
  have after_query_collision_simple:
    "hash_collision_budget
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      (mmap (ro_check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (ro_receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                'f protocol_channel) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    using after_query_collision[of idx] by simp
  have after_random_range:
    "hash_range_budget
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      ((let idx' = index (to_nat idx) in
          mmap (ro_check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (ro_receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  'f protocol_channel) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    for idx
    using after_query_range_simple[of "index (to_nat idx)"]
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
  have after_random_collision:
    "hash_collision_budget
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      ((let idx' = index (to_nat idx) in
          mmap (ro_check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (ro_receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  'f protocol_channel) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    for idx
    using after_query_collision_simple[of "index (to_nat idx)"]
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
  have "hash_collision_budget
      (1 + (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B)))
      (receive_query_index_challenge \<bind>
        (\<lambda>idx.
          let idx' = index (to_nat idx) in
          mmap (ro_check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (ro_receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  'f protocol_channel) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_receive_query_index_challenge
            hash_collision_budget_receive_query_index_challenge])
      (rule after_random_range, rule after_random_collision)
  then show ?thesis
    unfolding ro_verifier_query_round_program_def
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
qed

lemma hash_target_program_ro_verifier_query_round_program:
  assumes trace_len: "length f_fl \<le> ceil_log clength"
    and comp_len: "length fl \<le> ceil_log (maxDegree + 1)"
  shows "hash_target_program B ro_verifier_query_round_hash_budget
    (ro_verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?exact = "1 + ro_verifier_query_decommit_hash_budget +
    (length f_fl + length fl) * ro_verifier_fri_layer_hash_budget"
  have exact:
    "hash_target_program B ?exact
      (ro_verifier_query_round_program fr f_fl f_final as fl final)"
    by (rule hash_target_program_ro_verifier_query_round_program_exact)
  have len_le:
    "length f_fl + length fl \<le> ceil_log clength + ceil_log (maxDegree + 1)"
    using trace_len comp_len by simp
  have le: "?exact \<le> ro_verifier_query_round_hash_budget"
    unfolding ro_verifier_query_round_hash_budget_def
    using mult_right_mono[OF len_le, of ro_verifier_fri_layer_hash_budget]
    by simp
  show ?thesis
    by (rule hash_target_program_mono[OF le exact])
qed

lemma hash_range_budget_ro_verifier_query_round_program:
  assumes trace_len: "length f_fl \<le> ceil_log clength"
    and comp_len: "length fl \<le> ceil_log (maxDegree + 1)"
  shows "hash_range_budget ro_verifier_query_round_hash_budget
    (ro_verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?exact = "1 + ro_verifier_query_decommit_hash_budget +
    (length f_fl + length fl) * ro_verifier_fri_layer_hash_budget"
  have exact:
    "hash_range_budget ?exact
      (ro_verifier_query_round_program fr f_fl f_final as fl final)"
    by (rule hash_range_budget_ro_verifier_query_round_program_exact)
  have len_le:
    "length f_fl + length fl \<le> ceil_log clength + ceil_log (maxDegree + 1)"
    using trace_len comp_len by simp
  have le: "?exact \<le> ro_verifier_query_round_hash_budget"
    unfolding ro_verifier_query_round_hash_budget_def
    using mult_right_mono[OF len_le, of ro_verifier_fri_layer_hash_budget]
    by simp
  show ?thesis
    by (rule hash_range_budget_mono[OF le exact])
qed

lemma hash_collision_budget_ro_verifier_query_round_program:
  assumes trace_len: "length f_fl \<le> ceil_log clength"
    and comp_len: "length fl \<le> ceil_log (maxDegree + 1)"
  shows "hash_collision_budget ro_verifier_query_round_hash_budget
    (ro_verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?exact = "1 + ro_verifier_query_decommit_hash_budget +
    (length f_fl + length fl) * ro_verifier_fri_layer_hash_budget"
  have exact:
    "hash_collision_budget ?exact
      (ro_verifier_query_round_program fr f_fl f_final as fl final)"
    by (rule hash_collision_budget_ro_verifier_query_round_program_exact)
  have len_le:
    "length f_fl + length fl \<le> ceil_log clength + ceil_log (maxDegree + 1)"
    using trace_len comp_len by simp
  have le: "?exact \<le> ro_verifier_query_round_hash_budget"
    unfolding ro_verifier_query_round_hash_budget_def
    using mult_right_mono[OF len_le, of ro_verifier_fri_layer_hash_budget]
    by simp
  show ?thesis
    by (rule hash_collision_budget_mono[OF le exact])
qed

lemma hash_range_collision_budget_protocol_absorb_read:
  "hash_range_collision_budget 1
    (protocol_absorb_read :: ('f, 'f protocol_channel) state_monad)"
  by (rule hash_range_collision_budgetI)
    (rule hash_range_budget_protocol_absorb_read,
      rule hash_collision_budget_protocol_absorb_read)

lemma hash_range_collision_budget_mmap:
  fixes ms :: "('x, 'f protocol_channel) state_monad list"
  assumes ms: "\<And>m. m \<in> set ms \<Longrightarrow> hash_range_collision_budget n m"
  shows "hash_range_collision_budget (length ms * n) (mmap ms)"
proof (rule hash_range_collision_budgetI)
  show "hash_range_budget (length ms * n) (mmap ms)"
  proof (rule hash_range_budget_mmap)
    fix m
    assume m_in: "m \<in> set ms"
    show "hash_range_budget n m"
      by (rule hash_range_collision_budget_range[OF ms[OF m_in]])
  qed
  show "hash_collision_budget (length ms * n) (mmap ms)"
  proof (rule hash_collision_budget_mmap)
    fix m
    assume m_in: "m \<in> set ms"
    show "hash_range_budget n m"
      by (rule hash_range_collision_budget_range[OF ms[OF m_in]])
    show "hash_collision_budget n m"
      by (rule hash_range_collision_budget_collision[OF ms[OF m_in]])
  qed
qed

lemma hash_range_collision_budget_ntimes:
  fixes m :: "('x, 'f protocol_channel) state_monad"
  assumes m: "hash_range_collision_budget n m"
  shows "hash_range_collision_budget (k * n) (ntimes m k)"
proof (rule hash_range_collision_budgetI)
  show "hash_range_budget (k * n) (ntimes m k)"
    by (rule hash_range_budget_ntimes)
      (rule hash_range_collision_budget_range[OF m])
  show "hash_collision_budget (k * n) (ntimes m k)"
  proof (rule hash_collision_budget_ntimes)
    show "hash_range_budget n m"
      by (rule hash_range_collision_budget_range[OF m])
    show "hash_collision_budget n m"
      by (rule hash_range_collision_budget_collision[OF m])
  qed
qed

lemma hash_range_collision_budget_ro_receive_trace_fri_commits:
  "hash_range_collision_budget (1 + 1) ro_receive_trace_fri_commits"
  by (rule hash_range_collision_budgetI)
    (rule hash_range_budget_ro_receive_trace_fri_commits,
      rule hash_collision_budget_ro_receive_trace_fri_commits)

lemma hash_range_collision_budget_ro_receive_composition_fri_commits:
  "hash_range_collision_budget (1 + 1) ro_receive_composition_fri_commits"
  by (rule hash_range_collision_budgetI)
    (rule hash_range_budget_ro_receive_composition_fri_commits,
      rule hash_collision_budget_ro_receive_composition_fri_commits)

lemma hash_range_collision_budget_ro_alpha_round:
  "hash_range_collision_budget (1 + 1) ro_alpha_round"
  by (rule hash_range_collision_budgetI)
    (rule hash_range_budget_ro_alpha_round,
      rule hash_collision_budget_ro_alpha_round)

lemma hash_range_collision_budget_ntimes_ro_receive_trace_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_range_collision_budget (N * (1 + 1))
    (ntimes ro_receive_trace_fri_commits n)"
  by (rule hash_range_collision_budgetI)
    (rule hash_range_budget_ntimes_ro_receive_trace_fri_commits_bound[OF assms],
      rule hash_collision_budget_ntimes_ro_receive_trace_fri_commits_bound[OF assms])

lemma hash_range_collision_budget_ntimes_ro_receive_composition_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_range_collision_budget (N * (1 + 1))
    (ntimes ro_receive_composition_fri_commits n)"
  by (rule hash_range_collision_budgetI)
    (rule hash_range_budget_ntimes_ro_receive_composition_fri_commits_bound[OF assms],
      rule hash_collision_budget_ntimes_ro_receive_composition_fri_commits_bound[OF assms])

lemma hash_range_collision_budget_ro_verifier_query_round_program:
  assumes trace_len: "length f_fl \<le> ceil_log clength"
    and comp_len: "length fl \<le> ceil_log (maxDegree + 1)"
  shows "hash_range_collision_budget ro_verifier_query_round_hash_budget
    (ro_verifier_query_round_program fr f_fl f_final as fl final)"
  by (rule hash_range_collision_budgetI)
    (rule hash_range_budget_ro_verifier_query_round_program[OF trace_len comp_len],
      rule hash_collision_budget_ro_verifier_query_round_program[OF trace_len comp_len])

lemma hash_target_program_ro_verify_monad:
  "hash_target_program B ro_verifier_hash_query_budget ro_verify_monad"
proof -
  let ?Q = "rounds * ro_verifier_query_round_hash_budget"
  have alpha_map:
    "hash_target_program B (length spec * (1 + 1))
      (mmap (replicate (length spec) ro_alpha_round))"
  proof -
    let ?steps = "replicate (length spec) ro_alpha_round"
    have step_budget:
      "\<And>m. m \<in> set ?steps \<Longrightarrow> hash_target_program B (1 + 1) m"
    proof -
      fix m
      assume "m \<in> set ?steps"
      then have "m = ro_alpha_round"
        by simp
      then show "hash_target_program B (1 + 1) m"
        by (simp only: add_Suc_right add_0 hash_target_program_ro_alpha_round)
    qed
    have "hash_target_program B (length ?steps * (1 + 1)) (mmap ?steps)"
      by (rule hash_target_program_mmap) (rule step_budget)
    then show ?thesis by simp
  qed
  have after_final:
    "hash_target_program B (1 + ?Q)
      (protocol_absorb_read \<bind>
        (\<lambda>final. ntimes
          (ro_verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
    for fr f_fl f_final as fl
    by (rule hash_target_program_bind
        [OF hash_target_program_protocol_absorb_read
          hash_target_program_ntimes
            [OF hash_target_program_ro_verifier_query_round_program
              [OF len_f len_fl]]])
  have after_comp_fri:
    "hash_target_program B
      (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))
      ((ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
        (\<lambda>fl. protocol_absorb_read \<bind>
          (\<lambda>final. ntimes
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and dg_bound: "to_nat dg \<le> maxDegree"
    for fr f_fl f_final as dg
  proof (rule hash_target_program_bind_on_outcomes)
    show "hash_target_program B (ceil_log (maxDegree + 1) * (1 + 1))
      (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
        ((('f \<times> 'f) list), 'f protocol_channel) state_monad)"
      by (rule hash_target_program_ntimes_ro_receive_composition_fri_commits_bound)
        (rule ceil_log_to_nat_degree_bound[OF dg_bound])
    fix s fl t
    assume out:
      "Some (fl, t) \<in>
        set_dist (execute
          (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list), 'f protocol_channel) state_monad) s)"
    have len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
      using ntimes_outcome_length[OF out]
        ceil_log_to_nat_degree_bound[OF dg_bound]
      by simp
    show "hash_target_program B (1 + ?Q)
      (protocol_absorb_read \<bind>
        (\<lambda>final. ntimes
          (ro_verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
      by (rule after_final[OF len_f len_fl])
  qed
  have after_degree_assert:
    "hash_target_program B
      (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q)))
      (assert (to_nat dg \<le> maxDegree) \<bind>
        (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
          (\<lambda>fl. protocol_absorb_read \<bind>
            (\<lambda>final. ntimes
              (ro_verifier_query_round_program fr f_fl f_final as fl final)
              rounds))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as dg
  proof (rule hash_target_program_bind_on_outcomes)
    show "hash_target_program B 0
      (assert (to_nat dg \<le> maxDegree) ::
        (unit, 'f protocol_channel) state_monad)"
      by (rule hash_target_program_assert)
    fix s u t
    assume out:
      "Some (u, t) \<in>
        set_dist (execute
          (assert (to_nat dg \<le> maxDegree) ::
            (unit, 'f protocol_channel) state_monad) s)"
    have dg_bound: "to_nat dg \<le> maxDegree"
      using out unfolding assert_def
      by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
    show "hash_target_program B
      (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))
      ((ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
        (\<lambda>fl. protocol_absorb_read \<bind>
          (\<lambda>final. ntimes
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
      by (rule after_comp_fri[OF len_f dg_bound])
  qed
  have after_dg:
    "hash_target_program B
      (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))))
      (protocol_absorb_read \<bind>
        (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
          (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
            (\<lambda>fl. protocol_absorb_read \<bind>
              (\<lambda>final. ntimes
                (ro_verifier_query_round_program fr f_fl f_final as fl final)
                rounds)))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as
    by (rule hash_target_program_bind
        [OF hash_target_program_protocol_absorb_read after_degree_assert[OF len_f]])
  have after_alpha:
    "hash_target_program B
      (length spec * (1 + 1) +
        (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q)))))
      (mmap (replicate (length spec) ro_alpha_round) \<bind>
        (\<lambda>as. protocol_absorb_read \<bind>
          (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
            (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
              ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
              (\<lambda>fl. protocol_absorb_read \<bind>
                (\<lambda>final. ntimes
                  (ro_verifier_query_round_program fr f_fl f_final as fl final)
                  rounds))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final
    by (rule hash_target_program_bind
        [OF alpha_map after_dg[OF len_f]])
  have after_f_final:
    "hash_target_program B
      (1 + (length spec * (1 + 1) +
        (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))))))
      (protocol_absorb_read \<bind>
        (\<lambda>f_final. mmap (replicate (length spec) ro_alpha_round) \<bind>
          (\<lambda>as. protocol_absorb_read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
                (\<lambda>fl. protocol_absorb_read \<bind>
                  (\<lambda>final. ntimes
                    (ro_verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl
    by (rule hash_target_program_bind
        [OF hash_target_program_protocol_absorb_read after_alpha[OF len_f]])
  have after_trace_fri:
    "hash_target_program B
      (ceil_log clength * (1 + 1) +
        (1 + (length spec * (1 + 1) +
          (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q)))))))
      ((ntimes ro_receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
        (\<lambda>f_fl. protocol_absorb_read \<bind>
          (\<lambda>f_final. mmap (replicate (length spec) ro_alpha_round) \<bind>
            (\<lambda>as. protocol_absorb_read \<bind>
              (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                  ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
                  (\<lambda>fl. protocol_absorb_read \<bind>
                    (\<lambda>final. ntimes
                      (ro_verifier_query_round_program fr f_fl f_final as fl final)
                      rounds))))))))"
    for fr
  proof (rule hash_target_program_bind_on_outcomes)
    show "hash_target_program B (ceil_log clength * (1 + 1))
      (ntimes ro_receive_trace_fri_commits (ceil_log clength) ::
        ((('f \<times> 'f) list), 'f protocol_channel) state_monad)"
      by (rule hash_target_program_ntimes_ro_receive_trace_fri_commits_bound) simp
    fix s f_fl t
    assume out:
      "Some (f_fl, t) \<in>
        set_dist (execute
          (ntimes ro_receive_trace_fri_commits (ceil_log clength) ::
            ((('f \<times> 'f) list), 'f protocol_channel) state_monad) s)"
    have len_f: "length f_fl \<le> ceil_log clength"
      using ntimes_outcome_length[OF out] by simp
    show "hash_target_program B
      (1 + (length spec * (1 + 1) +
        (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))))))
      (protocol_absorb_read \<bind>
        (\<lambda>f_final. mmap (replicate (length spec) ro_alpha_round) \<bind>
          (\<lambda>as. protocol_absorb_read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
                (\<lambda>fl. protocol_absorb_read \<bind>
                  (\<lambda>final. ntimes
                    (ro_verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
      by (rule after_f_final[OF len_f])
  qed
  have top:
    "hash_target_program B
      (1 + (ceil_log clength * (1 + 1) +
        (1 + (length spec * (1 + 1) +
          (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))))))))
      (protocol_absorb_read \<bind>
        (\<lambda>fr. (ntimes ro_receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
          (\<lambda>f_fl. protocol_absorb_read \<bind>
            (\<lambda>f_final. mmap (replicate (length spec) ro_alpha_round) \<bind>
              (\<lambda>as. protocol_absorb_read \<bind>
                (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                  (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                    ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
                    (\<lambda>fl. protocol_absorb_read \<bind>
                      (\<lambda>final. ntimes
                        (ro_verifier_query_round_program fr f_fl f_final as fl final)
                        rounds)))))))))"
    by (rule hash_target_program_bind
        [OF hash_target_program_protocol_absorb_read after_trace_fri])
  let ?top_budget =
    "1 + (ceil_log clength * (1 + 1) +
      (1 + (length spec * (1 + 1) +
        (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q)))))))"
  have top': "hash_target_program B ?top_budget ro_verify_monad"
    using top
    unfolding ro_verify_monad_def
    by simp
  have budget_eq: "?top_budget = ro_verifier_hash_query_budget"
    unfolding ro_verifier_hash_query_budget_def
      ro_verifier_header_hash_budget_def verifier_header_hash_budget_def
    by (simp add: algebra_simps)
  show ?thesis
    using top' budget_eq by simp
qed

lemma hash_range_collision_budget_ro_verify_monad:
  "hash_range_collision_budget ro_verifier_hash_query_budget ro_verify_monad"
proof -
  let ?Q = "rounds * ro_verifier_query_round_hash_budget"
  have alpha_map:
    "hash_range_collision_budget (length spec * (1 + 1))
      (mmap (replicate (length spec) ro_alpha_round))"
  proof -
    let ?steps = "replicate (length spec) ro_alpha_round"
    have step_budget:
      "\<And>m. m \<in> set ?steps \<Longrightarrow> hash_range_collision_budget (1 + 1) m"
    proof -
      fix m
      assume "m \<in> set ?steps"
      then have "m = ro_alpha_round"
        by simp
      then show "hash_range_collision_budget (1 + 1) m"
        by (simp only: add_Suc_right add_0 hash_range_collision_budget_ro_alpha_round)
    qed
    have "hash_range_collision_budget (length ?steps * (1 + 1)) (mmap ?steps)"
      by (rule hash_range_collision_budget_mmap) (rule step_budget)
    then show ?thesis by simp
  qed
  have after_final:
    "hash_range_collision_budget (1 + ?Q)
      (protocol_absorb_read \<bind>
        (\<lambda>final. ntimes
          (ro_verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
    for fr f_fl f_final as fl
    by (rule hash_range_collision_budget_bind)
      (rule hash_range_collision_budget_protocol_absorb_read,
       rule hash_range_collision_budget_ntimes,
       rule hash_range_collision_budget_ro_verifier_query_round_program
        [OF len_f len_fl])
  have after_comp_fri:
    "hash_range_collision_budget
      (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))
      ((ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
        (\<lambda>fl. protocol_absorb_read \<bind>
          (\<lambda>final. ntimes
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and dg_bound: "to_nat dg \<le> maxDegree"
    for fr f_fl f_final as dg
  proof (rule hash_range_collision_budget_bind_on_outcomes)
    show "hash_range_collision_budget (ceil_log (maxDegree + 1) * (1 + 1))
      (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
        ((('f \<times> 'f) list), 'f protocol_channel) state_monad)"
      by (rule hash_range_collision_budget_ntimes_ro_receive_composition_fri_commits_bound)
        (rule ceil_log_to_nat_degree_bound[OF dg_bound])
    fix s fl t
    assume out:
      "Some (fl, t) \<in>
        set_dist (execute
          (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list), 'f protocol_channel) state_monad) s)"
    have len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
      using ntimes_outcome_length[OF out]
        ceil_log_to_nat_degree_bound[OF dg_bound]
      by simp
    show "hash_range_collision_budget (1 + ?Q)
      (protocol_absorb_read \<bind>
        (\<lambda>final. ntimes
          (ro_verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
      by (rule after_final[OF len_f len_fl])
  qed
  have after_degree_assert:
    "hash_range_collision_budget
      (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q)))
      (assert (to_nat dg \<le> maxDegree) \<bind>
        (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
          (\<lambda>fl. protocol_absorb_read \<bind>
            (\<lambda>final. ntimes
              (ro_verifier_query_round_program fr f_fl f_final as fl final)
              rounds))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as dg
  proof (rule hash_range_collision_budget_bind_on_outcomes)
    show "hash_range_collision_budget 0
      (assert (to_nat dg \<le> maxDegree) ::
        (unit, 'f protocol_channel) state_monad)"
      by (rule hash_range_collision_budgetI)
        (rule hash_range_budget_assert, rule hash_collision_budget_assert)
    fix s u t
    assume out:
      "Some (u, t) \<in>
        set_dist (execute
          (assert (to_nat dg \<le> maxDegree) ::
            (unit, 'f protocol_channel) state_monad) s)"
    have dg_bound: "to_nat dg \<le> maxDegree"
      using out unfolding assert_def
      by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
    show "hash_range_collision_budget
      (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))
      ((ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
        (\<lambda>fl. protocol_absorb_read \<bind>
          (\<lambda>final. ntimes
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
      by (rule after_comp_fri[OF len_f dg_bound])
  qed
  have after_dg:
    "hash_range_collision_budget
      (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))))
      (protocol_absorb_read \<bind>
        (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
          (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
            (\<lambda>fl. protocol_absorb_read \<bind>
              (\<lambda>final. ntimes
                (ro_verifier_query_round_program fr f_fl f_final as fl final)
                rounds)))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as
    by (rule hash_range_collision_budget_bind)
      (rule hash_range_collision_budget_protocol_absorb_read,
       rule after_degree_assert[OF len_f])
  have after_alpha:
    "hash_range_collision_budget
      (length spec * (1 + 1) +
        (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q)))))
      (mmap (replicate (length spec) ro_alpha_round) \<bind>
        (\<lambda>as. protocol_absorb_read \<bind>
          (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
            (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
              ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
              (\<lambda>fl. protocol_absorb_read \<bind>
                (\<lambda>final. ntimes
                  (ro_verifier_query_round_program fr f_fl f_final as fl final)
                  rounds))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final
    by (rule hash_range_collision_budget_bind)
      (rule alpha_map, rule after_dg[OF len_f])
  have after_f_final:
    "hash_range_collision_budget
      (1 + (length spec * (1 + 1) +
        (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))))))
      (protocol_absorb_read \<bind>
        (\<lambda>f_final. mmap (replicate (length spec) ro_alpha_round) \<bind>
          (\<lambda>as. protocol_absorb_read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
                (\<lambda>fl. protocol_absorb_read \<bind>
                  (\<lambda>final. ntimes
                    (ro_verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl
    by (rule hash_range_collision_budget_bind)
      (rule hash_range_collision_budget_protocol_absorb_read,
       rule after_alpha[OF len_f])
  have after_trace_fri:
    "hash_range_collision_budget
      (ceil_log clength * (1 + 1) +
        (1 + (length spec * (1 + 1) +
          (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q)))))))
      ((ntimes ro_receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
        (\<lambda>f_fl. protocol_absorb_read \<bind>
          (\<lambda>f_final. mmap (replicate (length spec) ro_alpha_round) \<bind>
            (\<lambda>as. protocol_absorb_read \<bind>
              (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                  ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
                  (\<lambda>fl. protocol_absorb_read \<bind>
                    (\<lambda>final. ntimes
                      (ro_verifier_query_round_program fr f_fl f_final as fl final)
                      rounds))))))))"
    for fr
  proof (rule hash_range_collision_budget_bind_on_outcomes)
    show "hash_range_collision_budget (ceil_log clength * (1 + 1))
      (ntimes ro_receive_trace_fri_commits (ceil_log clength) ::
        ((('f \<times> 'f) list), 'f protocol_channel) state_monad)"
      by (rule hash_range_collision_budget_ntimes_ro_receive_trace_fri_commits_bound) simp
    fix s f_fl t
    assume out:
      "Some (f_fl, t) \<in>
        set_dist (execute
          (ntimes ro_receive_trace_fri_commits (ceil_log clength) ::
            ((('f \<times> 'f) list), 'f protocol_channel) state_monad) s)"
    have len_f: "length f_fl \<le> ceil_log clength"
      using ntimes_outcome_length[OF out] by simp
    show "hash_range_collision_budget
      (1 + (length spec * (1 + 1) +
        (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))))))
      (protocol_absorb_read \<bind>
        (\<lambda>f_final. mmap (replicate (length spec) ro_alpha_round) \<bind>
          (\<lambda>as. protocol_absorb_read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
                (\<lambda>fl. protocol_absorb_read \<bind>
                  (\<lambda>final. ntimes
                    (ro_verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
      by (rule after_f_final[OF len_f])
  qed
  have top:
    "hash_range_collision_budget
      (1 + (ceil_log clength * (1 + 1) +
        (1 + (length spec * (1 + 1) +
          (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))))))))
      (protocol_absorb_read \<bind>
        (\<lambda>fr. (ntimes ro_receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
          (\<lambda>f_fl. protocol_absorb_read \<bind>
            (\<lambda>f_final. mmap (replicate (length spec) ro_alpha_round) \<bind>
              (\<lambda>as. protocol_absorb_read \<bind>
                (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                  (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                    ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
                    (\<lambda>fl. protocol_absorb_read \<bind>
                      (\<lambda>final. ntimes
                        (ro_verifier_query_round_program fr f_fl f_final as fl final)
                        rounds)))))))))"
    by (rule hash_range_collision_budget_bind)
      (rule hash_range_collision_budget_protocol_absorb_read,
       rule after_trace_fri)
  let ?top_budget =
    "1 + (ceil_log clength * (1 + 1) +
      (1 + (length spec * (1 + 1) +
        (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q)))))))"
  have top': "hash_range_collision_budget ?top_budget ro_verify_monad"
    using top
    unfolding ro_verify_monad_def
    by simp
  have budget_eq: "?top_budget = ro_verifier_hash_query_budget"
    unfolding ro_verifier_hash_query_budget_def
      ro_verifier_header_hash_budget_def verifier_header_hash_budget_def
    by (simp add: algebra_simps)
  show ?thesis
    using top' budget_eq by simp
qed

lemma hash_range_budget_ro_verify_monad:
  "hash_range_budget ro_verifier_hash_query_budget ro_verify_monad"
  by (rule hash_range_collision_budget_range
      [OF hash_range_collision_budget_ro_verify_monad])

lemma hash_collision_budget_ro_verify_monad:
  "hash_collision_budget ro_verifier_hash_query_budget ro_verify_monad"
  by (rule hash_range_collision_budget_collision
      [OF hash_range_collision_budget_ro_verify_monad])

definition ro_absorb_checked_staged_security_hash_query_budget_for ::
  "staged_budgets \<Rightarrow> nat" where
  "ro_absorb_checked_staged_security_hash_query_budget_for budgets =
    ro_checked_staged_transcript_hash_query_budget_for budgets +
    ro_verifier_hash_query_budget"

lemma hash_range_budget_ro_verifier_after_adversary:
  "hash_range_budget ro_verifier_hash_query_budget
    (verifier_state_transfer tr \<bind> (\<lambda>_. ro_verify_monad))"
proof -
  have "hash_range_budget (0 + ro_verifier_hash_query_budget)
    (verifier_state_transfer tr \<bind> (\<lambda>_. ro_verify_monad))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_verifier_state_transfer,
       rule hash_range_budget_ro_verify_monad)
  then show ?thesis by simp
qed

lemma hash_collision_budget_ro_verifier_after_adversary:
  "hash_collision_budget ro_verifier_hash_query_budget
    (verifier_state_transfer tr \<bind> (\<lambda>_. ro_verify_monad))"
proof -
  have "hash_collision_budget (0 + ro_verifier_hash_query_budget)
    (verifier_state_transfer tr \<bind> (\<lambda>_. ro_verify_monad))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_verifier_state_transfer,
       rule hash_collision_budget_verifier_state_transfer,
       rule hash_range_budget_ro_verify_monad,
       rule hash_collision_budget_ro_verify_monad)
  then show ?thesis by simp
qed

lemma hash_target_program_ro_verifier_after_adversary:
  "hash_target_program B ro_verifier_hash_query_budget
    (verifier_state_transfer tr \<bind> (\<lambda>_. ro_verify_monad))"
proof -
  have "hash_target_program B (0 + ro_verifier_hash_query_budget)
    (verifier_state_transfer tr \<bind> (\<lambda>_. ro_verify_monad))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_verifier_state_transfer,
       rule hash_target_program_ro_verify_monad)
  then show ?thesis by simp
qed

lemma hash_range_budget_ro_absorb_checked_staged_security_experiment:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      (ro_absorb_checked_staged_security_experiment A)"
proof -
  have cont:
    "\<And>data. hash_range_budget ro_verifier_hash_query_budget
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. ro_verify_monad)))"
    using hash_range_budget_ro_verifier_after_adversary
      [of "staged_proof_transcript data" for data]
    unfolding verifier_state_transfer_def sm_bind_assoc .
  have budget:
    "hash_range_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets +
        ro_verifier_hash_query_budget)
      (ro_absorb_checked_staged_security_experiment A)"
    unfolding ro_absorb_checked_staged_security_experiment_def
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_checked_staged_transcript_program
        [OF wf controlled], rule cont)
  then show ?thesis
    unfolding ro_absorb_checked_staged_security_hash_query_budget_for_def .
qed

lemma hash_collision_budget_ro_absorb_checked_staged_security_experiment:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_collision_budget
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      (ro_absorb_checked_staged_security_experiment A)"
proof -
  have cont_range:
    "\<And>data. hash_range_budget ro_verifier_hash_query_budget
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. ro_verify_monad)))"
    using hash_range_budget_ro_verifier_after_adversary
      [of "staged_proof_transcript data" for data]
    unfolding verifier_state_transfer_def sm_bind_assoc .
  have cont_collision:
    "\<And>data. hash_collision_budget ro_verifier_hash_query_budget
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. ro_verify_monad)))"
    using hash_collision_budget_ro_verifier_after_adversary
      [of "staged_proof_transcript data" for data]
    unfolding verifier_state_transfer_def sm_bind_assoc .
  have budget:
    "hash_collision_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets +
        ro_verifier_hash_query_budget)
      (ro_absorb_checked_staged_security_experiment A)"
    unfolding ro_absorb_checked_staged_security_experiment_def
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_ro_checked_staged_transcript_program
        [OF wf controlled],
       rule hash_collision_budget_ro_checked_staged_transcript_program
        [OF wf controlled],
       rule cont_range, rule cont_collision)
  then show ?thesis
    unfolding ro_absorb_checked_staged_security_hash_query_budget_for_def .
qed

lemma hash_target_program_ro_absorb_checked_staged_security_experiment:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      (ro_absorb_checked_staged_security_experiment A)"
proof -
  have cont:
    "\<And>data. hash_target_program B ro_verifier_hash_query_budget
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. ro_verify_monad)))"
    using hash_target_program_ro_verifier_after_adversary
      [of B "staged_proof_transcript data" for data]
    unfolding verifier_state_transfer_def sm_bind_assoc .
  have budget:
    "hash_target_program B
      (ro_checked_staged_transcript_hash_query_budget_for budgets +
        ro_verifier_hash_query_budget)
      (ro_absorb_checked_staged_security_experiment A)"
    unfolding ro_absorb_checked_staged_security_experiment_def
    by (rule hash_target_program_bind)
      (rule hash_target_program_ro_checked_staged_transcript_program
        [OF wf controlled], rule cont)
  then show ?thesis
    unfolding ro_absorb_checked_staged_security_hash_query_budget_for_def .
qed

lemma hash_range_budget_ro_absorb_checked_staged_security_experiment_with_data_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      (ro_absorb_checked_staged_security_experiment_with_data_state A)"
proof -
  let ?head = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have verify_return_range:
    "\<And>data saved. hash_range_budget (ro_verifier_hash_query_budget + 0)
      (ro_verify_monad \<bind>
        (\<lambda>result. return ((data, saved), result)))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_verify_monad, rule hash_range_budget_return)
  have cont_range:
    "\<And>data. hash_range_budget (0 + (ro_verifier_hash_query_budget + 0))
      (ro_checked_verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>saved. ro_verify_monad \<bind>
          (\<lambda>result. return ((data, saved), result))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_checked_verifier_state_transfer_with_saved,
        rule verify_return_range)
  have whole:
    "hash_range_budget
      (?head + (0 + (ro_verifier_hash_query_budget + 0)))
      (ro_checked_staged_transcript_program A \<bind>
        (\<lambda>data.
          ro_checked_verifier_state_transfer_with_saved
            (staged_proof_transcript data) \<bind>
          (\<lambda>saved. ro_verify_monad \<bind>
            (\<lambda>result. return ((data, saved), result)))))"
    by (rule hash_range_budget_bind)
      (rule
        hash_range_budget_ro_checked_staged_transcript_program[OF wf controlled],
        rule cont_range)
  show ?thesis
    using whole
    unfolding ro_absorb_checked_staged_security_experiment_with_data_state_def
      ro_checked_verifier_state_transfer_with_saved_def
      ro_absorb_checked_staged_security_hash_query_budget_for_def
    by (simp add: sm_bind_assoc add.assoc)
qed

lemma hash_collision_budget_ro_absorb_checked_staged_security_experiment_with_data_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_collision_budget
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      (ro_absorb_checked_staged_security_experiment_with_data_state A)"
proof -
  let ?head = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have verify_return_range:
    "\<And>data saved. hash_range_budget (ro_verifier_hash_query_budget + 0)
      (ro_verify_monad \<bind>
        (\<lambda>result. return ((data, saved), result)))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_verify_monad, rule hash_range_budget_return)
  have verify_return_collision:
    "\<And>data saved. hash_collision_budget (ro_verifier_hash_query_budget + 0)
      (ro_verify_monad \<bind>
        (\<lambda>result. return ((data, saved), result)))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_ro_verify_monad,
       rule hash_collision_budget_ro_verify_monad,
       rule hash_range_budget_return, rule hash_collision_budget_return)
  have cont_range:
    "\<And>data. hash_range_budget (0 + (ro_verifier_hash_query_budget + 0))
      (ro_checked_verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>saved. ro_verify_monad \<bind>
          (\<lambda>result. return ((data, saved), result))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_checked_verifier_state_transfer_with_saved,
        rule verify_return_range)
  have cont_collision:
    "\<And>data. hash_collision_budget (0 + (ro_verifier_hash_query_budget + 0))
      (ro_checked_verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>saved. ro_verify_monad \<bind>
          (\<lambda>result. return ((data, saved), result))))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_ro_checked_verifier_state_transfer_with_saved,
       rule hash_collision_budget_ro_checked_verifier_state_transfer_with_saved,
       rule verify_return_range, rule verify_return_collision)
  have whole:
    "hash_collision_budget
      (?head + (0 + (ro_verifier_hash_query_budget + 0)))
      (ro_checked_staged_transcript_program A \<bind>
        (\<lambda>data.
          ro_checked_verifier_state_transfer_with_saved
            (staged_proof_transcript data) \<bind>
          (\<lambda>saved. ro_verify_monad \<bind>
            (\<lambda>result. return ((data, saved), result)))))"
    by (rule hash_collision_budget_bind)
      (rule
        hash_range_budget_ro_checked_staged_transcript_program[OF wf controlled],
       rule
        hash_collision_budget_ro_checked_staged_transcript_program[OF wf controlled],
       rule cont_range, rule cont_collision)
  show ?thesis
    using whole
    unfolding ro_absorb_checked_staged_security_experiment_with_data_state_def
      ro_checked_verifier_state_transfer_with_saved_def
      ro_absorb_checked_staged_security_hash_query_budget_for_def
    by (simp add: sm_bind_assoc add.assoc)
qed

lemma hash_target_program_ro_absorb_checked_staged_security_experiment_with_data_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      (ro_absorb_checked_staged_security_experiment_with_data_state A)"
proof -
  let ?head = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have verify_return_target:
    "\<And>data saved. hash_target_program B (ro_verifier_hash_query_budget + 0)
      (ro_verify_monad \<bind>
        (\<lambda>result. return ((data, saved), result)))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_ro_verify_monad, rule hash_target_program_return)
  have cont_target:
    "\<And>data. hash_target_program B (0 + (ro_verifier_hash_query_budget + 0))
      (ro_checked_verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>saved. ro_verify_monad \<bind>
          (\<lambda>result. return ((data, saved), result))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_ro_checked_verifier_state_transfer_with_saved,
        rule verify_return_target)
  have whole:
    "hash_target_program B
      (?head + (0 + (ro_verifier_hash_query_budget + 0)))
      (ro_checked_staged_transcript_program A \<bind>
        (\<lambda>data.
          ro_checked_verifier_state_transfer_with_saved
            (staged_proof_transcript data) \<bind>
          (\<lambda>saved. ro_verify_monad \<bind>
            (\<lambda>result. return ((data, saved), result)))))"
    by (rule hash_target_program_bind)
      (rule
        hash_target_program_ro_checked_staged_transcript_program[OF wf controlled],
        rule cont_target)
  show ?thesis
    using whole
    unfolding ro_absorb_checked_staged_security_experiment_with_data_state_def
      ro_checked_verifier_state_transfer_with_saved_def
      ro_absorb_checked_staged_security_hash_query_budget_for_def
    by (simp add: sm_bind_assoc add.assoc)
qed

lemma ro_absorb_checked_staged_security_experiment_hash_new_collision_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (ro_absorb_checked_staged_security_experiment A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (ro_absorb_checked_staged_security_hash_query_budget_for budgets)"
proof -
  let ?q = "ro_absorb_checked_staged_security_hash_query_budget_for budgets"
  have collision_budget:
    "hash_collision_budget ?q (ro_absorb_checked_staged_security_experiment A)"
    by (rule hash_collision_budget_ro_absorb_checked_staged_security_experiment
        [OF wf controlled])
  have "wp_event (ro_absorb_checked_staged_security_experiment A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value
        (card (hash_map_output_values adversary_initial_state)) ?q"
    using collision_budget adversary_initial_state_no_output_collision
    unfolding hash_collision_budget_def by blast
  then show ?thesis by simp
qed

lemma ro_absorb_checked_staged_security_experiment_hash_map_output_collision_bad_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (ro_absorb_checked_staged_security_experiment A)
      (hash_map_output_collision_bad adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (ro_absorb_checked_staged_security_hash_query_budget_for budgets)"
proof -
  have "wp_event (ro_absorb_checked_staged_security_experiment A)
      (hash_map_output_collision_bad adversary_initial_state)
      adversary_initial_state \<le>
      wp_event (ro_absorb_checked_staged_security_experiment A)
        (hash_new_collision_event adversary_initial_state)
        adversary_initial_state"
    by (rule wp_event_mono)
      (rule hash_map_output_collision_bad_imp_security_new_collision)
  also have "... \<le>
      hash_collision_budget_value 0
        (ro_absorb_checked_staged_security_hash_query_budget_for budgets)"
    by (rule ro_absorb_checked_staged_security_experiment_hash_new_collision_bound_controlled
        [OF wf controlled])
  finally show ?thesis .
qed

end

end
