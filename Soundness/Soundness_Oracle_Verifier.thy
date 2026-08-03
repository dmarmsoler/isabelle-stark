(*  Title:      Stark/Soundness_Oracle_Verifier.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Oracle_Verifier
  imports Soundness_Oracle_Budgets
begin

text \<open>Concrete verifier hash-query budget bounds.\<close>

context soundness
begin

lemma ceil_log_mono:
  assumes "m \<le> n"
  shows "ceil_log m \<le> ceil_log n"
proof (cases "m \<le> 1")
  case True
  then show ?thesis
    unfolding ceil_log_def by simp
next
  case False
  then have m_pos: "0 < m" and m_minus: "m - 1 \<le> n - 1"
    using assms by simp_all
  have n_gt: "1 < n"
    using False assms by linarith
  have "floor_log (m - 1) \<le> floor_log (n - 1)"
    using floor_log_le_iff m_minus by blast
  then show ?thesis
    using False n_gt unfolding ceil_log_def by simp
qed

definition verifier_fri_layer_hash_budget :: nat
  where "verifier_fri_layer_hash_budget =
    Suc (floor_log (clength * scale)) + Suc (floor_log (clength * scale))"

definition verifier_query_decommit_hash_budget :: nat
  where "verifier_query_decommit_hash_budget =
    powers * Suc (floor_log (clength * scale))"

definition verifier_query_round_hash_budget :: nat
  where "verifier_query_round_hash_budget =
    1 + verifier_query_decommit_hash_budget +
      (ceil_log clength + ceil_log (maxDegree + 1)) *
        verifier_fri_layer_hash_budget"

definition verifier_header_hash_budget :: nat
  where "verifier_header_hash_budget =
    ceil_log clength + length spec + ceil_log (maxDegree + 1)"

definition verifier_hash_query_budget :: nat
  where "verifier_hash_query_budget =
    verifier_header_hash_budget + rounds * verifier_query_round_hash_budget"

definition concrete_merkle_binding_error :: prob
  where
    "concrete_merkle_binding_error =
      hash_collision_budget_value 0 verifier_hash_query_budget"

definition concrete_transcript_target_error :: "'f list \<Rightarrow> prob"
  where
    "concrete_transcript_target_error tr =
      nnreal (card (set tr) * verifier_hash_query_budget) / nnreal size"

lemma hash_target_program_alpha_challenge_step:
  "hash_target_program B 1
    (do {
      a0 \<leftarrow> receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    })"
proof -
  have assert_return:
    "hash_target_program B (0 + 0)
      (assert (a0 = a1) \<bind> (\<lambda>_. return a1) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for a0 a1
    by (rule hash_target_program_bind
        [OF hash_target_program_assert hash_target_program_return])
  have after_read:
    "hash_target_program B (0 + 0 + 0)
      (read \<bind> (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for a0
  proof -
    have "hash_target_program B (0 + (0 + 0))
      (read \<bind> (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_target_program_bind
          [OF hash_target_program_read assert_return])
    then show ?thesis by simp
  qed
  have "hash_target_program B (1 + (0 + 0 + 0))
      (receive_alpha_challenge \<bind>
        (\<lambda>a0. read \<bind> (\<lambda>a1.
          assert (a0 = a1) \<bind> (\<lambda>_. return a1))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_target_program_bind
        [OF hash_target_program_receive_alpha_challenge after_read])
  then show ?thesis
    by simp
qed

lemma hash_range_budget_alpha_challenge_step:
  "hash_range_budget 1
    (do {
      a0 \<leftarrow> receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    })"
proof -
  have assert_return:
    "hash_range_budget (0 + 0)
      (assert (a0 = a1) \<bind> (\<lambda>_. return a1) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)" for a0 a1
    by (rule hash_range_budget_bind
        [OF hash_range_budget_assert hash_range_budget_return])
  have after_read:
    "hash_range_budget (0 + 0 + 0)
      (read \<bind> (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)" for a0
  proof -
    have "hash_range_budget (0 + (0 + 0))
      (read \<bind> (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_bind
          [OF hash_range_budget_read assert_return])
    then show ?thesis by simp
  qed
  have "hash_range_budget (1 + (0 + 0 + 0))
      (receive_alpha_challenge \<bind>
        (\<lambda>a0. read \<bind> (\<lambda>a1.
          assert (a0 = a1) \<bind> (\<lambda>_. return a1))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_bind
        [OF hash_range_budget_receive_alpha_challenge after_read])
  then show ?thesis
    by simp
qed

lemma hash_collision_budget_alpha_challenge_step:
  "hash_collision_budget 1
    (do {
      a0 \<leftarrow> receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    })"
proof -
  have assert_return_range:
    "hash_range_budget (0 + 0)
      (assert (a0 = a1) \<bind> (\<lambda>_. return a1) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)" for a0 a1
    by (rule hash_range_budget_bind
        [OF hash_range_budget_assert hash_range_budget_return])
  have assert_return_coll:
    "hash_collision_budget (0 + 0)
      (assert (a0 = a1) \<bind> (\<lambda>_. return a1) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)" for a0 a1
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_assert hash_collision_budget_assert
          hash_range_budget_return hash_collision_budget_return])
  have after_read_range:
    "hash_range_budget (0 + 0 + 0)
      (read \<bind> (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)" for a0
  proof -
    have "hash_range_budget (0 + (0 + 0))
      (read \<bind> (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_bind
          [OF hash_range_budget_read assert_return_range])
    then show ?thesis by simp
  qed
  have after_read_coll:
    "hash_collision_budget (0 + 0 + 0)
      (read \<bind> (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)" for a0
  proof -
    have "hash_collision_budget (0 + (0 + 0))
      (read \<bind> (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_collision_budget_bind
          [OF hash_range_budget_read hash_collision_budget_read
            assert_return_range assert_return_coll])
    then show ?thesis by simp
  qed
  have "hash_collision_budget (1 + (0 + 0 + 0))
      (receive_alpha_challenge \<bind>
        (\<lambda>a0. read \<bind> (\<lambda>a1.
          assert (a0 = a1) \<bind> (\<lambda>_. return a1))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_receive_alpha_challenge
          hash_collision_budget_receive_alpha_challenge
          after_read_range after_read_coll])
  then show ?thesis
    by simp
qed

lemma hash_target_program_verifier_query_round_program_exact:
  "hash_target_program B
    (1 + verifier_query_decommit_hash_budget +
      (length f_fl + length fl) * verifier_fri_layer_hash_budget)
    (verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?L = "floor_log (clength * scale)"
  let ?B = "verifier_fri_layer_hash_budget"
  have B_eq: "?B = Suc ?L + Suc ?L"
    unfolding verifier_fri_layer_hash_budget_def by simp
  have after_comp:
    "hash_target_program B (length fl * ?B + 0)
      ((mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))"
    for idx fv
  proof (rule hash_target_program_bind)
    show "hash_target_program B (length fl * ?B)
      (mfold
        (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
        (receive_query_commits fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
      unfolding B_eq
      by (rule hash_target_program_receive_query_commits_mfold) simp
    show "\<And>x. hash_target_program B 0
      ((case x of (i, x, len, pw) \<Rightarrow> assert (x = final)) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (simp add: hash_target_program_assert split: prod.splits)
  qed
  have after_trace_assert:
    "hash_target_program B (0 + (length fl * ?B + 0))
      ((assert (f_x = f_final) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final))))"
    for idx fv f_i f_x f_len f_pow
    by (rule hash_target_program_bind
        [OF hash_target_program_assert after_comp])
  have after_trace:
    "hash_target_program B
      (length f_fl * ?B + (0 + (length fl * ?B + 0)))
      ((mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pow).
          assert (f_x = f_final) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final)))))"
    for idx fv
  proof (rule hash_target_program_bind)
    show "hash_target_program B (length f_fl * ?B)
      (mfold (idx, hd fv, clength * scale, 1)
        (receive_query_commits f_fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
      unfolding B_eq
      by (rule hash_target_program_receive_query_commits_mfold) simp
    fix x :: "nat \<times> 'f \<times> nat \<times> nat"
    obtain f_i f_x f_len f_pow where x_eq:
      "x = (f_i, f_x, f_len, f_pow)"
      by (cases x) auto
    have case_budget:
      "hash_target_program B (0 + (length fl * ?B + 0))
        ((assert (f_x = f_final) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))"
      by (rule hash_target_program_bind
          [OF hash_target_program_assert after_comp])
    show "hash_target_program B (0 + (length fl * ?B + 0))
      ((case x of (f_i, f_x, f_len, f_pow) \<Rightarrow>
        assert (f_x = f_final) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final)))) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      using case_budget
      unfolding x_eq
      by (simp split: prod.splits)
  qed
  have after_query:
    "hash_target_program B
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + (0 + (length fl * ?B + 0))))
      (mmap (check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
  proof -
    have decommit:
      "hash_target_program B verifier_query_decommit_hash_budget
        (mmap (check_decommit_on_query fr idx))"
    proof -
      have exact:
        "hash_target_program B
          (powers * Suc (floor_log (scale * clength)))
          (mmap (check_decommit_on_query fr idx))"
        by (rule hash_target_program_check_decommit_on_query)
      show ?thesis
        using exact
        unfolding verifier_query_decommit_hash_budget_def
        by (simp add: mult.commute)
    qed
    show ?thesis
      by (rule hash_target_program_bind[OF decommit after_trace])
  qed
  have after_query_simple:
    "hash_target_program B
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      (mmap (check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    using after_query[of idx] by simp
  have after_random:
    "hash_target_program B
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      ((let idx' = index (to_nat idx) in
          mmap (check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    for idx
    using after_query_simple[of "index (to_nat idx)"]
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
  have "hash_target_program B
      (1 + (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B)))
      (receive_query_index_challenge \<bind>
        (\<lambda>idx.
          let idx' = index (to_nat idx) in
          mmap (check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    by (rule hash_target_program_bind
        [OF hash_target_program_receive_query_index_challenge])
      (rule after_random)
  then show ?thesis
    unfolding verifier_query_round_program_def
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
qed


lemma hash_range_budget_verifier_query_round_program_exact:
  "hash_range_budget
    (1 + verifier_query_decommit_hash_budget +
      (length f_fl + length fl) * verifier_fri_layer_hash_budget)
    (verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?L = "floor_log (clength * scale)"
  let ?B = "verifier_fri_layer_hash_budget"
  have B_eq: "?B = Suc ?L + Suc ?L"
    unfolding verifier_fri_layer_hash_budget_def by simp
  have after_comp:
    "hash_range_budget (length fl * ?B + 0)
      ((mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))"
    for idx fv
  proof (rule hash_range_budget_bind)
    show "hash_range_budget (length fl * ?B)
      (mfold
        (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
        (receive_query_commits fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
      unfolding B_eq
      by (rule hash_range_budget_receive_query_commits_mfold) simp
    show "\<And>x. hash_range_budget 0
      ((case x of (i, x, len, pw) \<Rightarrow> assert (x = final)) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (simp add: hash_range_budget_assert split: prod.splits)
  qed
  have after_trace_assert:
    "hash_range_budget (0 + (length fl * ?B + 0))
      ((assert (f_x = f_final) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final))))"
    for idx fv f_i f_x f_len f_pow
    by (rule hash_range_budget_bind
        [OF hash_range_budget_assert after_comp])
  have after_trace:
    "hash_range_budget
      (length f_fl * ?B + (0 + (length fl * ?B + 0)))
      ((mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pow).
          assert (f_x = f_final) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final)))))"
    for idx fv
  proof (rule hash_range_budget_bind)
    show "hash_range_budget (length f_fl * ?B)
      (mfold (idx, hd fv, clength * scale, 1)
        (receive_query_commits f_fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
      unfolding B_eq
      by (rule hash_range_budget_receive_query_commits_mfold) simp
    fix x :: "nat \<times> 'f \<times> nat \<times> nat"
    obtain f_i f_x f_len f_pow where x_eq:
      "x = (f_i, f_x, f_len, f_pow)"
      by (cases x) auto
    have case_budget:
      "hash_range_budget (0 + (length fl * ?B + 0))
        ((assert (f_x = f_final) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))"
      by (rule hash_range_budget_bind
          [OF hash_range_budget_assert after_comp])
    show "hash_range_budget (0 + (length fl * ?B + 0))
      ((case x of (f_i, f_x, f_len, f_pow) \<Rightarrow>
        assert (f_x = f_final) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final)))) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      using case_budget
      unfolding x_eq
      by (simp split: prod.splits)
  qed
  have after_query:
    "hash_range_budget
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + (0 + (length fl * ?B + 0))))
      (mmap (check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
  proof -
    have decommit:
      "hash_range_budget verifier_query_decommit_hash_budget
        (mmap (check_decommit_on_query fr idx))"
    proof -
      have exact:
        "hash_range_budget
          (powers * Suc (floor_log (scale * clength)))
          (mmap (check_decommit_on_query fr idx))"
        by (rule hash_range_budget_check_decommit_on_query)
      show ?thesis
        using exact
        unfolding verifier_query_decommit_hash_budget_def
        by (simp add: mult.commute)
    qed
    show ?thesis
      by (rule hash_range_budget_bind[OF decommit after_trace])
  qed
  have after_query_simple:
    "hash_range_budget
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      (mmap (check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    using after_query[of idx] by simp
  have after_random:
    "hash_range_budget
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      ((let idx' = index (to_nat idx) in
          mmap (check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    for idx
    using after_query_simple[of "index (to_nat idx)"]
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
  have "hash_range_budget
      (1 + (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B)))
      (receive_query_index_challenge \<bind>
        (\<lambda>idx.
          let idx' = index (to_nat idx) in
          mmap (check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    by (rule hash_range_budget_bind
        [OF hash_range_budget_receive_query_index_challenge])
      (rule after_random)
  then show ?thesis
    unfolding verifier_query_round_program_def
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
qed

lemma hash_target_program_verifier_query_round_program:
  assumes len_f: "length f_fl \<le> ceil_log clength"
    and len_c: "length fl \<le> ceil_log (maxDegree + 1)"
  shows
    "hash_target_program B verifier_query_round_hash_budget
      (verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?N = "verifier_fri_layer_hash_budget"
  have exact:
    "hash_target_program B
      (1 + verifier_query_decommit_hash_budget +
        (length f_fl + length fl) * ?N)
      (verifier_query_round_program fr f_fl f_final as fl final)"
    by (rule hash_target_program_verifier_query_round_program_exact)
  have le:
    "1 + verifier_query_decommit_hash_budget +
        (length f_fl + length fl) * ?N
      \<le> verifier_query_round_hash_budget"
    using len_f len_c
    unfolding verifier_query_round_hash_budget_def
    by simp
  show ?thesis
    by (rule hash_target_program_mono[OF le exact])
qed

lemma hash_range_budget_verifier_query_round_program:
  assumes len_f: "length f_fl \<le> ceil_log clength"
    and len_c: "length fl \<le> ceil_log (maxDegree + 1)"
  shows
    "hash_range_budget verifier_query_round_hash_budget
      (verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?B = "verifier_fri_layer_hash_budget"
  have exact:
    "hash_range_budget
      (1 + verifier_query_decommit_hash_budget +
        (length f_fl + length fl) * ?B)
      (verifier_query_round_program fr f_fl f_final as fl final)"
    by (rule hash_range_budget_verifier_query_round_program_exact)
  have le:
    "1 + verifier_query_decommit_hash_budget +
        (length f_fl + length fl) * ?B
      \<le> verifier_query_round_hash_budget"
    using len_f len_c
    unfolding verifier_query_round_hash_budget_def
    by simp
  show ?thesis
    by (rule hash_range_budget_mono[OF le exact])
qed

lemma hash_collision_budget_verifier_query_round_program_exact:
  "hash_collision_budget
    (1 + verifier_query_decommit_hash_budget +
      (length f_fl + length fl) * verifier_fri_layer_hash_budget)
    (verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?L = "floor_log (clength * scale)"
  let ?B = "verifier_fri_layer_hash_budget"
  have B_eq: "?B = Suc ?L + Suc ?L"
    unfolding verifier_fri_layer_hash_budget_def by simp
  have after_comp_range:
    "hash_range_budget (length fl * ?B + 0)
      ((mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))"
    for idx fv
  proof (rule hash_range_budget_bind)
    show "hash_range_budget (length fl * ?B)
      (mfold
        (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
        (receive_query_commits fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
      unfolding B_eq
      by (rule hash_range_budget_receive_query_commits_mfold) simp
    show "\<And>x. hash_range_budget 0
      ((case x of (i, x, len, pw) \<Rightarrow> assert (x = final)) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (simp add: hash_range_budget_assert split: prod.splits)
  qed
  have after_comp_coll:
    "hash_collision_budget (length fl * ?B + 0)
      ((mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))"
    for idx fv
  proof (rule hash_collision_budget_bind)
    show "hash_range_budget (length fl * ?B)
      (mfold
        (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
        (receive_query_commits fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
      unfolding B_eq
      by (rule hash_range_budget_receive_query_commits_mfold) simp
    show "hash_collision_budget (length fl * ?B)
      (mfold
        (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
        (receive_query_commits fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
      unfolding B_eq
      by (rule hash_collision_budget_receive_query_commits_mfold) simp
    show "\<And>x. hash_range_budget 0
      ((case x of (i, x, len, pw) \<Rightarrow> assert (x = final)) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (simp add: hash_range_budget_assert split: prod.splits)
    show "\<And>x. hash_collision_budget 0
      ((case x of (i, x, len, pw) \<Rightarrow> assert (x = final)) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (simp add: hash_collision_budget_assert split: prod.splits)
  qed
  have trace_cont_range:
    "hash_range_budget (0 + (length fl * ?B + 0))
      ((assert (f_x = f_final) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final))))"
    for idx fv f_x
    by (rule hash_range_budget_bind
        [OF hash_range_budget_assert after_comp_range])
  have trace_cont_coll:
    "hash_collision_budget (0 + (length fl * ?B + 0))
      ((assert (f_x = f_final) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final))))"
    for idx fv f_x
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_assert hash_collision_budget_assert
          after_comp_range after_comp_coll])
  have after_trace_range:
    "hash_range_budget
      (length f_fl * ?B + (0 + (length fl * ?B + 0)))
      ((mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>(f_i, f_x, f_len, fpw).
          assert (f_x = f_final) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final)))))"
    for idx fv
  proof (rule hash_range_budget_bind)
    show "hash_range_budget (length f_fl * ?B)
      (mfold (idx, hd fv, clength * scale, 1)
        (receive_query_commits f_fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
      unfolding B_eq
      by (rule hash_range_budget_receive_query_commits_mfold) simp
    fix x :: "nat \<times> 'f \<times> nat \<times> nat"
    obtain f_i f_x f_len fpw where x_eq: "x = (f_i, f_x, f_len, fpw)"
      by (cases x) auto
    have case_budget:
      "hash_range_budget (0 + (length fl * ?B + 0))
        ((assert (f_x = f_final) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))"
      by (rule trace_cont_range)
    show "hash_range_budget (0 + (length fl * ?B + 0))
      ((case x of (f_i, f_x, f_len, fpw) \<Rightarrow>
        assert (f_x = f_final) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final)))) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      using case_budget unfolding x_eq by (simp split: prod.splits)
  qed
  have after_trace_coll:
    "hash_collision_budget
      (length f_fl * ?B + (0 + (length fl * ?B + 0)))
      ((mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>(f_i, f_x, f_len, fpw).
          assert (f_x = f_final) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final)))))"
    for idx fv
  proof (rule hash_collision_budget_bind)
    show "hash_range_budget (length f_fl * ?B)
      (mfold (idx, hd fv, clength * scale, 1)
        (receive_query_commits f_fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
      unfolding B_eq
      by (rule hash_range_budget_receive_query_commits_mfold) simp
    show "hash_collision_budget (length f_fl * ?B)
      (mfold (idx, hd fv, clength * scale, 1)
        (receive_query_commits f_fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
      unfolding B_eq
      by (rule hash_collision_budget_receive_query_commits_mfold) simp
    fix x :: "nat \<times> 'f \<times> nat \<times> nat"
    obtain f_i f_x f_len fpw where x_eq: "x = (f_i, f_x, f_len, fpw)"
      by (cases x) auto
    have range_case:
      "hash_range_budget (0 + (length fl * ?B + 0))
        ((assert (f_x = f_final) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))"
      by (rule trace_cont_range)
    show "hash_range_budget (0 + (length fl * ?B + 0))
      ((case x of (f_i, f_x, f_len, fpw) \<Rightarrow>
        assert (f_x = f_final) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final)))) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      using range_case unfolding x_eq by (simp split: prod.splits)
    have coll_case:
      "hash_collision_budget (0 + (length fl * ?B + 0))
        ((assert (f_x = f_final) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))"
      by (rule trace_cont_coll)
    show "hash_collision_budget (0 + (length fl * ?B + 0))
      ((case x of (f_i, f_x, f_len, fpw) \<Rightarrow>
        assert (f_x = f_final) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final)))) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      using coll_case unfolding x_eq by (simp split: prod.splits)
  qed
  have after_query_range:
    "hash_range_budget
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + (0 + (length fl * ?B + 0))))
      (mmap (check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, fpw).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
  proof -
    have decommit:
      "hash_range_budget verifier_query_decommit_hash_budget
        (mmap (check_decommit_on_query fr idx))"
    proof -
      have exact:
        "hash_range_budget
          (powers * Suc (floor_log (scale * clength)))
          (mmap (check_decommit_on_query fr idx))"
        by (rule hash_range_budget_check_decommit_on_query)
      show ?thesis
        using exact
        unfolding verifier_query_decommit_hash_budget_def
        by (simp add: mult.commute)
    qed
    show ?thesis
      by (rule hash_range_budget_bind[OF decommit after_trace_range])
  qed
  have after_query_coll:
    "hash_collision_budget
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + (0 + (length fl * ?B + 0))))
      (mmap (check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, fpw).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
  proof -
    have decommit_range:
      "hash_range_budget verifier_query_decommit_hash_budget
        (mmap (check_decommit_on_query fr idx))"
    proof -
      have exact:
        "hash_range_budget
          (powers * Suc (floor_log (scale * clength)))
          (mmap (check_decommit_on_query fr idx))"
        by (rule hash_range_budget_check_decommit_on_query)
      show ?thesis
        using exact
        unfolding verifier_query_decommit_hash_budget_def
        by (simp add: mult.commute)
    qed
    have decommit_coll:
      "hash_collision_budget verifier_query_decommit_hash_budget
        (mmap (check_decommit_on_query fr idx))"
    proof -
      have exact:
        "hash_collision_budget
          (powers * Suc (floor_log (scale * clength)))
          (mmap (check_decommit_on_query fr idx))"
        by (rule hash_collision_budget_check_decommit_on_query)
      show ?thesis
        using exact
        unfolding verifier_query_decommit_hash_budget_def
        by (simp add: mult.commute)
    qed
    show ?thesis
      by (rule hash_collision_budget_bind
          [OF decommit_range decommit_coll after_trace_range after_trace_coll])
  qed
  have after_query_range_simple:
    "hash_range_budget
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      (mmap (check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, fpw).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    using after_query_range[of idx] by simp
  have after_query_coll_simple:
    "hash_collision_budget
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      (mmap (check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, fpw).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    using after_query_coll[of idx] by simp
  have after_random_range:
    "hash_range_budget
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      ((let idx' = index (to_nat idx) in
          mmap (check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, fpw).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    for idx
    using after_query_range_simple[of "index (to_nat idx)"]
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
  have after_random_coll:
    "hash_collision_budget
      (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      ((let idx' = index (to_nat idx) in
          mmap (check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, fpw).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    for idx
    using after_query_coll_simple[of "index (to_nat idx)"]
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
  have "hash_collision_budget
      (1 + (verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B)))
      (receive_query_index_challenge \<bind>
        (\<lambda>idx.
          let idx' = index (to_nat idx) in
          mmap (check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, fpw).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_receive_query_index_challenge
          hash_collision_budget_receive_query_index_challenge])
      (rule after_random_range, rule after_random_coll)
  then show ?thesis
    unfolding verifier_query_round_program_def
    by (simp add: Let_def algebra_simps mult.commute split: prod.splits)
qed

lemma hash_collision_budget_verifier_query_round_program:
  assumes len_f: "length f_fl \<le> ceil_log clength"
    and len_c: "length fl \<le> ceil_log (maxDegree + 1)"
  shows
    "hash_collision_budget verifier_query_round_hash_budget
      (verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?B = "verifier_fri_layer_hash_budget"
  have exact:
    "hash_collision_budget
      (1 + verifier_query_decommit_hash_budget +
        (length f_fl + length fl) * ?B)
      (verifier_query_round_program fr f_fl f_final as fl final)"
    by (rule hash_collision_budget_verifier_query_round_program_exact)
  have le:
    "1 + verifier_query_decommit_hash_budget +
        (length f_fl + length fl) * ?B
      \<le> verifier_query_round_hash_budget"
    using len_f len_c
    unfolding verifier_query_round_hash_budget_def
    by simp
  show ?thesis
    by (rule hash_collision_budget_mono[OF le exact])
qed

lemma ceil_log_to_nat_degree_bound:
  assumes "to_nat dg \<le> maxDegree"
  shows "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
  by (rule ceil_log_mono) (use assms in simp)

lemma hash_range_budget_ntimes_receive_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_range_budget N (ntimes receive_fri_commits n)"
proof -
  have exact: "hash_range_budget (n * 1) (ntimes receive_fri_commits n)"
    by (rule hash_range_budget_ntimes[OF hash_range_budget_receive_fri_commits])
  show ?thesis
    by (rule hash_range_budget_mono[OF _ exact]) (use assms in simp)
qed

lemma hash_target_program_ntimes_receive_trace_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_target_program B N (ntimes receive_trace_fri_commits n)"
proof -
  have exact:
    "hash_target_program B (n * 1) (ntimes receive_trace_fri_commits n)"
    by (rule hash_target_program_ntimes
        [OF hash_target_program_receive_trace_fri_commits])
  show ?thesis
    by (rule hash_target_program_mono[OF _ exact]) (use assms in simp)
qed

lemma hash_target_program_ntimes_receive_composition_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_target_program B N (ntimes receive_composition_fri_commits n)"
proof -
  have exact:
    "hash_target_program B (n * 1) (ntimes receive_composition_fri_commits n)"
    by (rule hash_target_program_ntimes
        [OF hash_target_program_receive_composition_fri_commits])
  show ?thesis
    by (rule hash_target_program_mono[OF _ exact]) (use assms in simp)
qed

lemma hash_target_program_alpha_round:
  "hash_target_program B 1 alpha_round"
  unfolding alpha_round_def
  by (rule hash_target_program_alpha_challenge_step)

lemma hash_target_program_verify_monad:
  "hash_target_program B verifier_hash_query_budget verify_monad"
proof -
  let ?Q = "rounds * verifier_query_round_hash_budget"
  have alpha_map_range:
    "hash_target_program B (length spec)
      (mmap (replicate (length spec)
        (alpha_round ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)))"
  proof -
    let ?steps =
      "replicate (length spec)
        (alpha_round ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    have step_range:
      "\<And>m. m \<in> set ?steps \<Longrightarrow> hash_target_program B 1 m"
    proof -
      fix m
      assume "m \<in> set ?steps"
      then have m_eq:
        "m =
          (alpha_round ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
        by simp
      show "hash_target_program B 1 m"
        unfolding m_eq
        by (rule hash_target_program_alpha_round)
    qed
    have "hash_target_program B (length ?steps * 1) (mmap ?steps)"
      by (rule hash_target_program_mmap)
        (rule step_range)
    then show ?thesis by simp
  qed
  have after_final:
    "hash_target_program B (0 + ?Q)
      (read \<bind>
        (\<lambda>final. ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
    for fr f_fl f_final as fl
    by (rule hash_target_program_bind
        [OF hash_target_program_read
          hash_target_program_ntimes
            [OF hash_target_program_verifier_query_round_program
              [OF len_f len_fl]]])
  have after_comp_fri:
    "hash_target_program B (ceil_log (maxDegree + 1) + (0 + ?Q))
      ((ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>fl. read \<bind>
          (\<lambda>final. ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and dg_bound: "to_nat dg \<le> maxDegree"
    for fr f_fl f_final as dg
  proof (rule hash_target_program_bind_on_outcomes)
    show "hash_target_program B (ceil_log (maxDegree + 1))
      (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
        ((('f \<times> 'f) list),
          ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_target_program_ntimes_receive_composition_fri_commits_bound)
        (rule ceil_log_to_nat_degree_bound[OF dg_bound])
    fix s fl t
    assume out:
      "Some (fl, t) \<in>
        set_dist (execute
          (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list),
              ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
      using ntimes_receive_composition_fri_commits_outcome[OF out]
        ceil_log_to_nat_degree_bound[OF dg_bound]
      by simp
    show "hash_target_program B (0 + ?Q)
      (read \<bind>
        (\<lambda>final. ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
      by (rule after_final[OF len_f len_fl])
  qed
  have after_degree_assert:
    "hash_target_program B (0 + (ceil_log (maxDegree + 1) + (0 + ?Q)))
      (assert (to_nat dg \<le> maxDegree) \<bind>
        (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>fl. read \<bind>
            (\<lambda>final. ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as dg
  proof (rule hash_target_program_bind_on_outcomes)
    show "hash_target_program B 0
      (assert (to_nat dg \<le> maxDegree) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_target_program_assert)
    fix s u t
    assume out:
      "Some (u, t) \<in>
        set_dist (execute
          (assert (to_nat dg \<le> maxDegree) ::
            (unit, ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have dg_bound: "to_nat dg \<le> maxDegree"
      using out unfolding assert_def
      by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
    show "hash_target_program B (ceil_log (maxDegree + 1) + (0 + ?Q))
      ((ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>fl. read \<bind>
          (\<lambda>final. ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
      by (rule after_comp_fri[OF len_f dg_bound])
  qed
  have after_read_dg:
    "hash_target_program B
      (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))
      (read \<bind>
        (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
          (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list),
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>fl. read \<bind>
              (\<lambda>final. ntimes
                (verifier_query_round_program fr f_fl f_final as fl final)
                rounds)))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as
    by (rule hash_target_program_bind
        [OF hash_target_program_read after_degree_assert[OF len_f]])
  have after_alpha:
    "hash_target_program B
      (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q)))))
      (mmap (replicate (length spec) alpha_round) \<bind>
        (\<lambda>as. read \<bind>
          (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
            (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
              ((('f \<times> 'f) list),
                ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>fl. read \<bind>
                (\<lambda>final. ntimes
                  (verifier_query_round_program fr f_fl f_final as fl final)
                  rounds))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final
    by (rule hash_target_program_bind
        [OF alpha_map_range after_read_dg[OF len_f]])
  have after_read_f_final:
    "hash_target_program B
      (0 + (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))
      (read \<bind>
        (\<lambda>f_final. mmap (replicate (length spec) alpha_round) \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list),
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final. ntimes
                    (verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl
    by (rule hash_target_program_bind
        [OF hash_target_program_read after_alpha[OF len_f]])
  have after_trace_fri:
    "hash_target_program B
      (ceil_log clength +
        (0 + (length spec +
          (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q)))))))
      ((ntimes receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>f_fl. read \<bind>
          (\<lambda>f_final. mmap (replicate (length spec) alpha_round) \<bind>
            (\<lambda>as. read \<bind>
              (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                  ((('f \<times> 'f) list),
                    ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                  (\<lambda>fl. read \<bind>
                    (\<lambda>final. ntimes
                      (verifier_query_round_program fr f_fl f_final as fl final)
                      rounds))))))))"
    for fr
  proof (rule hash_target_program_bind_on_outcomes)
    show "hash_target_program B (ceil_log clength)
      (ntimes receive_trace_fri_commits (ceil_log clength) ::
        ((('f \<times> 'f) list),
          ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_target_program_ntimes_receive_trace_fri_commits_bound) simp
    fix s f_fl t
    assume out:
      "Some (f_fl, t) \<in>
        set_dist (execute
          (ntimes receive_trace_fri_commits (ceil_log clength) ::
            ((('f \<times> 'f) list),
              ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have len_f: "length f_fl \<le> ceil_log clength"
      using ntimes_receive_trace_fri_commits_outcome[OF out] by simp
    show "hash_target_program B
      (0 + (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))
      (read \<bind>
        (\<lambda>f_final. mmap (replicate (length spec) alpha_round) \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list),
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final. ntimes
                    (verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
      by (rule after_read_f_final[OF len_f])
  qed
  have top:
    "hash_target_program B
      (0 + (ceil_log clength +
        (0 + (length spec +
          (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))))
      (read \<bind>
        (\<lambda>fr. (ntimes receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>f_fl. read \<bind>
            (\<lambda>f_final. mmap (replicate (length spec) alpha_round) \<bind>
              (\<lambda>as. read \<bind>
                (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                  (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                    ((('f \<times> 'f) list),
                      ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                    (\<lambda>fl. read \<bind>
                      (\<lambda>final. ntimes
                        (verifier_query_round_program fr f_fl f_final as fl final)
                        rounds)))))))))"
    by (rule hash_target_program_bind
        [OF hash_target_program_read after_trace_fri])
  show ?thesis
    using top
    unfolding verify_monad_def verifier_query_round_program_def alpha_round_def
      verifier_hash_query_budget_def verifier_header_hash_budget_def
    by (simp add: algebra_simps)
qed

lemma hash_target_budget_verify_monad:
  "hash_target_budget B verifier_hash_query_budget verify_monad"
  by (rule hash_target_program_budget[OF hash_target_program_verify_monad])

lemma wp_verify_monad_hash_new_output_hit_bound:
  "wp_event verify_monad (hash_new_output_hit_event B s) s \<le>
    hash_target_budget_value B verifier_hash_query_budget"
  using hash_target_budget_verify_monad
  unfolding hash_target_budget_def by blast

lemma wp_verify_monad_transcript_hash_target_hit_bound:
  "wp_event verify_monad
      (hash_new_output_hit_event (set tr) (verifier_initial_state tr))
      (verifier_initial_state tr)
    \<le> nnreal (card (set tr) * verifier_hash_query_budget) / nnreal size"
  using wp_verify_monad_hash_new_output_hit_bound
    [of "set tr" "verifier_initial_state tr"]
  unfolding hash_target_budget_value_def
  by (simp add: mult.commute)


lemma hash_range_budget_ntimes_receive_trace_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_range_budget N (ntimes receive_trace_fri_commits n)"
proof -
  have exact:
    "hash_range_budget (n * 1) (ntimes receive_trace_fri_commits n)"
    by (rule hash_range_budget_ntimes
        [OF hash_range_budget_receive_trace_fri_commits])
  show ?thesis
    by (rule hash_range_budget_mono[OF _ exact]) (use assms in simp)
qed

lemma hash_range_budget_ntimes_receive_composition_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_range_budget N (ntimes receive_composition_fri_commits n)"
proof -
  have exact:
    "hash_range_budget (n * 1) (ntimes receive_composition_fri_commits n)"
    by (rule hash_range_budget_ntimes
        [OF hash_range_budget_receive_composition_fri_commits])
  show ?thesis
    by (rule hash_range_budget_mono[OF _ exact]) (use assms in simp)
qed

lemma hash_range_budget_alpha_round:
  "hash_range_budget 1 alpha_round"
  unfolding alpha_round_def
  by (rule hash_range_budget_alpha_challenge_step)

lemma hash_range_budget_verify_monad:
  "hash_range_budget verifier_hash_query_budget verify_monad"
proof -
  let ?Q = "rounds * verifier_query_round_hash_budget"
  have alpha_map_range:
    "hash_range_budget (length spec)
      (mmap (replicate (length spec)
        (alpha_round ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)))"
  proof -
    let ?steps =
      "replicate (length spec)
        (alpha_round ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    have step_range:
      "\<And>m. m \<in> set ?steps \<Longrightarrow> hash_range_budget 1 m"
    proof -
      fix m
      assume "m \<in> set ?steps"
      then have m_eq:
        "m =
          (alpha_round ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
        by simp
      show "hash_range_budget 1 m"
        unfolding m_eq
        by (rule hash_range_budget_alpha_round)
    qed
    have "hash_range_budget (length ?steps * 1) (mmap ?steps)"
      by (rule hash_range_budget_mmap)
        (rule step_range)
    then show ?thesis by simp
  qed
  have after_final:
    "hash_range_budget (0 + ?Q)
      (read \<bind>
        (\<lambda>final. ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
    for fr f_fl f_final as fl
    by (rule hash_range_budget_bind
        [OF hash_range_budget_read
          hash_range_budget_ntimes
            [OF hash_range_budget_verifier_query_round_program
              [OF len_f len_fl]]])
  have after_comp_fri:
    "hash_range_budget (ceil_log (maxDegree + 1) + (0 + ?Q))
      ((ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>fl. read \<bind>
          (\<lambda>final. ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and dg_bound: "to_nat dg \<le> maxDegree"
    for fr f_fl f_final as dg
  proof (rule hash_range_budget_bind_on_outcomes)
    show "hash_range_budget (ceil_log (maxDegree + 1))
      (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
        ((('f \<times> 'f) list),
          ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_ntimes_receive_composition_fri_commits_bound)
        (rule ceil_log_to_nat_degree_bound[OF dg_bound])
    fix s fl t
    assume out:
      "Some (fl, t) \<in>
        set_dist (execute
          (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list),
              ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
      using ntimes_receive_composition_fri_commits_outcome[OF out]
        ceil_log_to_nat_degree_bound[OF dg_bound]
      by simp
    show "hash_range_budget (0 + ?Q)
      (read \<bind>
        (\<lambda>final. ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
      by (rule after_final[OF len_f len_fl])
  qed
  have after_degree_assert:
    "hash_range_budget (0 + (ceil_log (maxDegree + 1) + (0 + ?Q)))
      (assert (to_nat dg \<le> maxDegree) \<bind>
        (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>fl. read \<bind>
            (\<lambda>final. ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as dg
  proof (rule hash_range_budget_bind_on_outcomes)
    show "hash_range_budget 0
      (assert (to_nat dg \<le> maxDegree) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_assert)
    fix s u t
    assume out:
      "Some (u, t) \<in>
        set_dist (execute
          (assert (to_nat dg \<le> maxDegree) ::
            (unit, ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have dg_bound: "to_nat dg \<le> maxDegree"
      using out unfolding assert_def
      by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
    show "hash_range_budget (ceil_log (maxDegree + 1) + (0 + ?Q))
      ((ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>fl. read \<bind>
          (\<lambda>final. ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
      by (rule after_comp_fri[OF len_f dg_bound])
  qed
  have after_read_dg:
    "hash_range_budget
      (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))
      (read \<bind>
        (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
          (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list),
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>fl. read \<bind>
              (\<lambda>final. ntimes
                (verifier_query_round_program fr f_fl f_final as fl final)
                rounds)))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as
    by (rule hash_range_budget_bind
        [OF hash_range_budget_read after_degree_assert[OF len_f]])
  have after_alpha:
    "hash_range_budget
      (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q)))))
      (mmap (replicate (length spec) alpha_round) \<bind>
        (\<lambda>as. read \<bind>
          (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
            (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
              ((('f \<times> 'f) list),
                ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>fl. read \<bind>
                (\<lambda>final. ntimes
                  (verifier_query_round_program fr f_fl f_final as fl final)
                  rounds))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final
    by (rule hash_range_budget_bind
        [OF alpha_map_range after_read_dg[OF len_f]])
  have after_read_f_final:
    "hash_range_budget
      (0 + (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))
      (read \<bind>
        (\<lambda>f_final. mmap (replicate (length spec) alpha_round) \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list),
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final. ntimes
                    (verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl
    by (rule hash_range_budget_bind
        [OF hash_range_budget_read after_alpha[OF len_f]])
  have after_trace_fri:
    "hash_range_budget
      (ceil_log clength +
        (0 + (length spec +
          (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q)))))))
      ((ntimes receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>f_fl. read \<bind>
          (\<lambda>f_final. mmap (replicate (length spec) alpha_round) \<bind>
            (\<lambda>as. read \<bind>
              (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                  ((('f \<times> 'f) list),
                    ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                  (\<lambda>fl. read \<bind>
                    (\<lambda>final. ntimes
                      (verifier_query_round_program fr f_fl f_final as fl final)
                      rounds))))))))"
    for fr
  proof (rule hash_range_budget_bind_on_outcomes)
    show "hash_range_budget (ceil_log clength)
      (ntimes receive_trace_fri_commits (ceil_log clength) ::
        ((('f \<times> 'f) list),
          ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_ntimes_receive_trace_fri_commits_bound) simp
    fix s f_fl t
    assume out:
      "Some (f_fl, t) \<in>
        set_dist (execute
          (ntimes receive_trace_fri_commits (ceil_log clength) ::
            ((('f \<times> 'f) list),
              ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have len_f: "length f_fl \<le> ceil_log clength"
      using ntimes_receive_trace_fri_commits_outcome[OF out] by simp
    show "hash_range_budget
      (0 + (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))
      (read \<bind>
        (\<lambda>f_final. mmap (replicate (length spec) alpha_round) \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list),
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final. ntimes
                    (verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
      by (rule after_read_f_final[OF len_f])
  qed
  have top:
    "hash_range_budget
      (0 + (ceil_log clength +
        (0 + (length spec +
          (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))))
      (read \<bind>
        (\<lambda>fr. (ntimes receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>f_fl. read \<bind>
            (\<lambda>f_final. mmap (replicate (length spec) alpha_round) \<bind>
              (\<lambda>as. read \<bind>
                (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                  (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                    ((('f \<times> 'f) list),
                      ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                    (\<lambda>fl. read \<bind>
                      (\<lambda>final. ntimes
                        (verifier_query_round_program fr f_fl f_final as fl final)
                        rounds)))))))))"
    by (rule hash_range_budget_bind
        [OF hash_range_budget_read after_trace_fri])
  show ?thesis
    using top
    unfolding verify_monad_def verifier_query_round_program_def alpha_round_def
      verifier_hash_query_budget_def verifier_header_hash_budget_def
    by (simp add: algebra_simps)
qed

lemma hash_collision_budget_ntimes_receive_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_collision_budget N (ntimes receive_fri_commits n)"
proof -
  have exact: "hash_collision_budget (n * 1) (ntimes receive_fri_commits n)"
    by (rule hash_collision_budget_ntimes
        [OF hash_range_budget_receive_fri_commits
          hash_collision_budget_receive_fri_commits])
  show ?thesis
    by (rule hash_collision_budget_mono[OF _ exact]) (use assms in simp)
qed

lemma hash_collision_budget_ntimes_receive_trace_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_collision_budget N (ntimes receive_trace_fri_commits n)"
proof -
  have exact:
    "hash_collision_budget (n * 1) (ntimes receive_trace_fri_commits n)"
    by (rule hash_collision_budget_ntimes
        [OF hash_range_budget_receive_trace_fri_commits
          hash_collision_budget_receive_trace_fri_commits])
  show ?thesis
    by (rule hash_collision_budget_mono[OF _ exact]) (use assms in simp)
qed

lemma hash_collision_budget_ntimes_receive_composition_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_collision_budget N (ntimes receive_composition_fri_commits n)"
proof -
  have exact:
    "hash_collision_budget (n * 1)
      (ntimes receive_composition_fri_commits n)"
    by (rule hash_collision_budget_ntimes
        [OF hash_range_budget_receive_composition_fri_commits
          hash_collision_budget_receive_composition_fri_commits])
  show ?thesis
    by (rule hash_collision_budget_mono[OF _ exact]) (use assms in simp)
qed

lemma hash_collision_budget_alpha_round:
  "hash_collision_budget 1 alpha_round"
  unfolding alpha_round_def
  by (rule hash_collision_budget_alpha_challenge_step)

lemma hash_collision_budget_verify_monad:
  "hash_collision_budget verifier_hash_query_budget verify_monad"
proof -
  let ?Q = "rounds * verifier_query_round_hash_budget"
  let ?alpha_steps =
    "replicate (length spec)
      (alpha_round ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
  have alpha_step_range:
    "\<And>m. m \<in> set ?alpha_steps \<Longrightarrow> hash_range_budget 1 m"
  proof -
    fix m
    assume "m \<in> set ?alpha_steps"
    then have m_eq:
      "m =
        (alpha_round ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      by simp
    show "hash_range_budget 1 m"
      unfolding m_eq by (rule hash_range_budget_alpha_round)
  qed
  have alpha_step_coll:
    "\<And>m. m \<in> set ?alpha_steps \<Longrightarrow> hash_collision_budget 1 m"
  proof -
    fix m
    assume "m \<in> set ?alpha_steps"
    then have m_eq:
      "m =
        (alpha_round ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      by simp
    show "hash_collision_budget 1 m"
      unfolding m_eq by (rule hash_collision_budget_alpha_round)
  qed
  have alpha_map_range:
    "hash_range_budget (length spec) (mmap ?alpha_steps)"
  proof -
    have "hash_range_budget (length ?alpha_steps * 1) (mmap ?alpha_steps)"
      by (rule hash_range_budget_mmap) (rule alpha_step_range)
    then show ?thesis by simp
  qed
  have alpha_map_coll:
    "hash_collision_budget (length spec) (mmap ?alpha_steps)"
  proof -
    have "hash_collision_budget (length ?alpha_steps * 1) (mmap ?alpha_steps)"
    proof (rule hash_collision_budget_mmap)
      fix m
      assume m_in: "m \<in> set ?alpha_steps"
      show "hash_range_budget 1 m"
        by (rule alpha_step_range[OF m_in])
      show "hash_collision_budget 1 m"
        by (rule alpha_step_coll[OF m_in])
    qed
    then show ?thesis by simp
  qed
  have after_final_range:
    "hash_range_budget (0 + ?Q)
      (read \<bind>
        (\<lambda>final. ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
    for fr f_fl f_final as fl
    by (rule hash_range_budget_bind
        [OF hash_range_budget_read
          hash_range_budget_ntimes
            [OF hash_range_budget_verifier_query_round_program
              [OF len_f len_fl]]])
  have after_final_coll:
    "hash_collision_budget (0 + ?Q)
      (read \<bind>
        (\<lambda>final. ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
    for fr f_fl f_final as fl
  proof -
    have query_range:
      "\<And>final. hash_range_budget verifier_query_round_hash_budget
        (verifier_query_round_program fr f_fl f_final as fl final)"
      by (rule hash_range_budget_verifier_query_round_program
          [OF len_f len_fl])
    have query_coll:
      "\<And>final. hash_collision_budget verifier_query_round_hash_budget
        (verifier_query_round_program fr f_fl f_final as fl final)"
      by (rule hash_collision_budget_verifier_query_round_program
          [OF len_f len_fl])
    have rounds_range:
      "\<And>final. hash_range_budget ?Q
        (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
          rounds)"
      by (rule hash_range_budget_ntimes) (rule query_range)
    have rounds_coll:
      "\<And>final. hash_collision_budget ?Q
        (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
          rounds)"
      by (rule hash_collision_budget_ntimes)
        (rule query_range, rule query_coll)
    show ?thesis
      by (rule hash_collision_budget_bind
          [OF hash_range_budget_read hash_collision_budget_read
            rounds_range rounds_coll])
  qed
  have after_comp_fri_range:
    "hash_range_budget (ceil_log (maxDegree + 1) + (0 + ?Q))
      ((ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>fl. read \<bind>
          (\<lambda>final. ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and dg_bound: "to_nat dg \<le> maxDegree"
    for fr f_fl f_final as dg
  proof (rule hash_range_budget_bind_on_outcomes)
    show "hash_range_budget (ceil_log (maxDegree + 1))
      (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
        ((('f \<times> 'f) list),
          ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_ntimes_receive_composition_fri_commits_bound)
        (rule ceil_log_to_nat_degree_bound[OF dg_bound])
    fix s fl t
    assume out:
      "Some (fl, t) \<in>
        set_dist (execute
          (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list),
              ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
      using ntimes_receive_composition_fri_commits_outcome[OF out]
        ceil_log_to_nat_degree_bound[OF dg_bound]
      by simp
    show "hash_range_budget (0 + ?Q)
      (read \<bind>
        (\<lambda>final. ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
      by (rule after_final_range[OF len_f len_fl])
  qed
  have after_comp_fri_coll:
    "hash_collision_budget (ceil_log (maxDegree + 1) + (0 + ?Q))
      ((ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>fl. read \<bind>
          (\<lambda>final. ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and dg_bound: "to_nat dg \<le> maxDegree"
    for fr f_fl f_final as dg
  proof (rule hash_collision_budget_bind_on_outcomes)
    show "hash_range_budget (ceil_log (maxDegree + 1))
      (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
        ((('f \<times> 'f) list),
          ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_ntimes_receive_composition_fri_commits_bound)
        (rule ceil_log_to_nat_degree_bound[OF dg_bound])
    show "hash_collision_budget (ceil_log (maxDegree + 1))
      (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
        ((('f \<times> 'f) list),
          ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_collision_budget_ntimes_receive_composition_fri_commits_bound)
        (rule ceil_log_to_nat_degree_bound[OF dg_bound])
    fix s fl t
    assume out:
      "Some (fl, t) \<in>
        set_dist (execute
          (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list),
              ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
      using ntimes_receive_composition_fri_commits_outcome[OF out]
        ceil_log_to_nat_degree_bound[OF dg_bound]
      by simp
    show "hash_range_budget (0 + ?Q)
      (read \<bind>
        (\<lambda>final. ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
      by (rule after_final_range[OF len_f len_fl])
    show "hash_collision_budget (0 + ?Q)
      (read \<bind>
        (\<lambda>final. ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
      by (rule after_final_coll[OF len_f len_fl])
  qed
  have after_degree_assert_range:
    "hash_range_budget (0 + (ceil_log (maxDegree + 1) + (0 + ?Q)))
      (assert (to_nat dg \<le> maxDegree) \<bind>
        (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>fl. read \<bind>
            (\<lambda>final. ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as dg
  proof (rule hash_range_budget_bind_on_outcomes)
    show "hash_range_budget 0
      (assert (to_nat dg \<le> maxDegree) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_assert)
    fix s u t
    assume out:
      "Some (u, t) \<in>
        set_dist (execute
          (assert (to_nat dg \<le> maxDegree) ::
            (unit, ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have dg_bound: "to_nat dg \<le> maxDegree"
      using out unfolding assert_def
      by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
    show "hash_range_budget (ceil_log (maxDegree + 1) + (0 + ?Q))
      ((ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>fl. read \<bind>
          (\<lambda>final. ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
      by (rule after_comp_fri_range[OF len_f dg_bound])
  qed
  have after_degree_assert_coll:
    "hash_collision_budget (0 + (ceil_log (maxDegree + 1) + (0 + ?Q)))
      (assert (to_nat dg \<le> maxDegree) \<bind>
        (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>fl. read \<bind>
            (\<lambda>final. ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as dg
  proof (rule hash_collision_budget_bind_on_outcomes)
    show "hash_range_budget 0
      (assert (to_nat dg \<le> maxDegree) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_assert)
    show "hash_collision_budget 0
      (assert (to_nat dg \<le> maxDegree) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_collision_budget_assert)
    fix s u t
    assume out:
      "Some (u, t) \<in>
        set_dist (execute
          (assert (to_nat dg \<le> maxDegree) ::
            (unit, ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have dg_bound: "to_nat dg \<le> maxDegree"
      using out unfolding assert_def
      by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
    show "hash_range_budget (ceil_log (maxDegree + 1) + (0 + ?Q))
      ((ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>fl. read \<bind>
          (\<lambda>final. ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
      by (rule after_comp_fri_range[OF len_f dg_bound])
    show "hash_collision_budget (ceil_log (maxDegree + 1) + (0 + ?Q))
      ((ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>fl. read \<bind>
          (\<lambda>final. ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
      by (rule after_comp_fri_coll[OF len_f dg_bound])
  qed
  have after_read_dg_range:
    "hash_range_budget
      (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))
      (read \<bind>
        (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
          (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list),
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>fl. read \<bind>
              (\<lambda>final. ntimes
                (verifier_query_round_program fr f_fl f_final as fl final)
                rounds)))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as
    by (rule hash_range_budget_bind
        [OF hash_range_budget_read after_degree_assert_range[OF len_f]])
  have after_read_dg_coll:
    "hash_collision_budget
      (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))
      (read \<bind>
        (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
          (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list),
              ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>fl. read \<bind>
              (\<lambda>final. ntimes
                (verifier_query_round_program fr f_fl f_final as fl final)
                rounds)))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_read hash_collision_budget_read
          after_degree_assert_range[OF len_f]
          after_degree_assert_coll[OF len_f]])
  have after_alpha_range:
    "hash_range_budget
      (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q)))))
      (mmap ?alpha_steps \<bind>
        (\<lambda>as. read \<bind>
          (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
            (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
              ((('f \<times> 'f) list),
                ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>fl. read \<bind>
                (\<lambda>final. ntimes
                  (verifier_query_round_program fr f_fl f_final as fl final)
                  rounds))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final
    by (rule hash_range_budget_bind
        [OF alpha_map_range after_read_dg_range[OF len_f]])
  have after_alpha_coll:
    "hash_collision_budget
      (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q)))))
      (mmap ?alpha_steps \<bind>
        (\<lambda>as. read \<bind>
          (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
            (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
              ((('f \<times> 'f) list),
                ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>fl. read \<bind>
                (\<lambda>final. ntimes
                  (verifier_query_round_program fr f_fl f_final as fl final)
                  rounds))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final
    by (rule hash_collision_budget_bind
        [OF alpha_map_range alpha_map_coll
          after_read_dg_range[OF len_f] after_read_dg_coll[OF len_f]])
  have after_read_f_final_range:
    "hash_range_budget
      (0 + (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))
      (read \<bind>
        (\<lambda>f_final. mmap ?alpha_steps \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list),
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final. ntimes
                    (verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl
    by (rule hash_range_budget_bind
        [OF hash_range_budget_read after_alpha_range[OF len_f]])
  have after_read_f_final_coll:
    "hash_collision_budget
      (0 + (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))
      (read \<bind>
        (\<lambda>f_final. mmap ?alpha_steps \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list),
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final. ntimes
                    (verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_read hash_collision_budget_read
          after_alpha_range[OF len_f] after_alpha_coll[OF len_f]])
  have after_trace_fri_range:
    "hash_range_budget
      (ceil_log clength +
        (0 + (length spec +
          (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q)))))))
      ((ntimes receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>f_fl. read \<bind>
          (\<lambda>f_final. mmap ?alpha_steps \<bind>
            (\<lambda>as. read \<bind>
              (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                  ((('f \<times> 'f) list),
                    ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                  (\<lambda>fl. read \<bind>
                    (\<lambda>final. ntimes
                      (verifier_query_round_program fr f_fl f_final as fl final)
                      rounds))))))))"
    for fr
  proof (rule hash_range_budget_bind_on_outcomes)
    show "hash_range_budget (ceil_log clength)
      (ntimes receive_trace_fri_commits (ceil_log clength) ::
        ((('f \<times> 'f) list),
          ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_ntimes_receive_trace_fri_commits_bound) simp
    fix s f_fl t
    assume out:
      "Some (f_fl, t) \<in>
        set_dist (execute
          (ntimes receive_trace_fri_commits (ceil_log clength) ::
            ((('f \<times> 'f) list),
              ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have len_f: "length f_fl \<le> ceil_log clength"
      using ntimes_receive_trace_fri_commits_outcome[OF out] by simp
    show "hash_range_budget
      (0 + (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))
      (read \<bind>
        (\<lambda>f_final. mmap ?alpha_steps \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list),
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final. ntimes
                    (verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
      by (rule after_read_f_final_range[OF len_f])
  qed
  have after_trace_fri_coll:
    "hash_collision_budget
      (ceil_log clength +
        (0 + (length spec +
          (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q)))))))
      ((ntimes receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>f_fl. read \<bind>
          (\<lambda>f_final. mmap ?alpha_steps \<bind>
            (\<lambda>as. read \<bind>
              (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                  ((('f \<times> 'f) list),
                    ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                  (\<lambda>fl. read \<bind>
                    (\<lambda>final. ntimes
                      (verifier_query_round_program fr f_fl f_final as fl final)
                      rounds))))))))"
    for fr
  proof (rule hash_collision_budget_bind_on_outcomes)
    show "hash_range_budget (ceil_log clength)
      (ntimes receive_trace_fri_commits (ceil_log clength) ::
        ((('f \<times> 'f) list),
          ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_ntimes_receive_trace_fri_commits_bound) simp
    show "hash_collision_budget (ceil_log clength)
      (ntimes receive_trace_fri_commits (ceil_log clength) ::
        ((('f \<times> 'f) list),
          ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_collision_budget_ntimes_receive_trace_fri_commits_bound) simp
    fix s f_fl t
    assume out:
      "Some (f_fl, t) \<in>
        set_dist (execute
          (ntimes receive_trace_fri_commits (ceil_log clength) ::
            ((('f \<times> 'f) list),
              ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have len_f: "length f_fl \<le> ceil_log clength"
      using ntimes_receive_trace_fri_commits_outcome[OF out] by simp
    show "hash_range_budget
      (0 + (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))
      (read \<bind>
        (\<lambda>f_final. mmap ?alpha_steps \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list),
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final. ntimes
                    (verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
      by (rule after_read_f_final_range[OF len_f])
    show "hash_collision_budget
      (0 + (length spec +
        (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))
      (read \<bind>
        (\<lambda>f_final. mmap ?alpha_steps \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list),
                  ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final. ntimes
                    (verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
      by (rule after_read_f_final_coll[OF len_f])
  qed
  have top_range:
    "hash_range_budget
      (0 + (ceil_log clength +
        (0 + (length spec +
          (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))))
      (read \<bind>
        (\<lambda>fr. (ntimes receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>f_fl. read \<bind>
            (\<lambda>f_final. mmap ?alpha_steps \<bind>
              (\<lambda>as. read \<bind>
                (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                  (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                    ((('f \<times> 'f) list),
                      ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                    (\<lambda>fl. read \<bind>
                      (\<lambda>final. ntimes
                        (verifier_query_round_program fr f_fl f_final as fl final)
                        rounds)))))))))"
    by (rule hash_range_budget_bind
        [OF hash_range_budget_read after_trace_fri_range])
  have top_coll:
    "hash_collision_budget
      (0 + (ceil_log clength +
        (0 + (length spec +
          (0 + (0 + (ceil_log (maxDegree + 1) + (0 + ?Q))))))))
      (read \<bind>
        (\<lambda>fr. (ntimes receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list),
            ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>f_fl. read \<bind>
            (\<lambda>f_final. mmap ?alpha_steps \<bind>
              (\<lambda>as. read \<bind>
                (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                  (\<lambda>_. (ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                    ((('f \<times> 'f) list),
                      ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
                    (\<lambda>fl. read \<bind>
                      (\<lambda>final. ntimes
                        (verifier_query_round_program fr f_fl f_final as fl final)
                        rounds)))))))))"
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_read hash_collision_budget_read
          after_trace_fri_range after_trace_fri_coll])
  show ?thesis
    using top_coll
    unfolding verify_monad_def verifier_query_round_program_def alpha_round_def
      verifier_hash_query_budget_def verifier_header_hash_budget_def
    by (simp add: algebra_simps)
qed

end

end
