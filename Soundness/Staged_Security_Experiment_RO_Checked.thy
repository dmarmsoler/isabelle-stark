theory Staged_Security_Experiment_RO_Checked
  imports Staged_Security_Experiment_RO_Transcript_Collision_Budgets
begin

context soundness
begin

definition ro_receive_fri_commits_with
  :: "('f, 'f protocol_channel) state_monad \<Rightarrow>
      ('f \<times> 'f, 'f protocol_channel) state_monad"
  where
    "ro_receive_fri_commits_with receive_challenge =
      do {
        r \<leftarrow> protocol_absorb_read;
        b \<leftarrow> receive_challenge;
        return (b, r)
      }"

definition ro_receive_trace_fri_commits
  :: "('f \<times> 'f, 'f protocol_channel) state_monad"
  where
    "ro_receive_trace_fri_commits =
      ro_receive_fri_commits_with receive_trace_fri_challenge"

definition ro_receive_composition_fri_commits
  :: "('f \<times> 'f, 'f protocol_channel) state_monad"
  where
    "ro_receive_composition_fri_commits =
      ro_receive_fri_commits_with receive_composition_fri_challenge"

definition ro_query_decommitment_step
  :: "'f \<Rightarrow> nat \<Rightarrow> ('f, 'f protocol_channel) state_monad"
  where
    "ro_query_decommitment_step fr i = (do {
      qh \<leftarrow> protocol_absorb_read;
      let len = scale * clength;
      qh_path \<leftarrow> ntimes protocol_absorb_read (floor_log len);
      ap \<leftarrow> check_authentication_path len i qh qh_path;
      assert (ap = fr);
      return qh
    })"

definition ro_check_decommit_on_query
  :: "'f \<Rightarrow> nat \<Rightarrow> ('f, 'f protocol_channel) state_monad list"
  where
    "ro_check_decommit_on_query fr idx =
      map (ro_query_decommitment_step fr) (powers_scaled idx)"

definition ro_fri_layer_opening_step
  :: "'f \<times> 'f \<Rightarrow> nat \<times> 'f \<times> nat \<times> nat \<Rightarrow>
      (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad"
  where
    "ro_fri_layer_opening_step bf st =
      (case bf of (b, f) \<Rightarrow> case st of (i, x, len, pw) \<Rightarrow> do {
        xp \<leftarrow> protocol_absorb_read;
        xp_path \<leftarrow> ntimes protocol_absorb_read (floor_log len);
        xn \<leftarrow> protocol_absorb_read;
        xn_path \<leftarrow> ntimes protocol_absorb_read (floor_log len);
        fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path
      })"

definition ro_receive_query_commits
  where
    "ro_receive_query_commits fl = map ro_fri_layer_opening_step fl"

definition ro_alpha_round
  :: "('f, 'f protocol_channel) state_monad"
  where
    "ro_alpha_round = (do {
      a0 \<leftarrow> receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> protocol_absorb_read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    })"

definition ro_verifier_query_round_program
  :: "'f \<Rightarrow> ('f \<times> 'f) list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> ('f \<times> 'f) list \<Rightarrow> 'f \<Rightarrow>
      (unit, 'f protocol_channel) state_monad"
  where
    "ro_verifier_query_round_program fr f_fl f_final as fl final = (do {
      idx \<leftarrow> receive_query_index_challenge;
      let idx' = index (to_nat idx);
      fv \<leftarrow> mmap (ro_check_decommit_on_query fr idx');

      (f_i, f_x, f_len, f_pow) \<leftarrow>
        mfold (idx', hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl);
      assert (f_x = f_final);

      (i, x, len, pow) \<leftarrow>
        mfold (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
          (ro_receive_query_commits fl);

      assert (x = final)
    })"

definition ro_verify_monad
  :: "(unit list, 'f protocol_channel) state_monad"
  where
    "ro_verify_monad = (do {
      fr \<leftarrow> protocol_absorb_read;
      f_fl \<leftarrow> ntimes ro_receive_trace_fri_commits (ceil_log clength);
      f_final \<leftarrow> protocol_absorb_read;
      as \<leftarrow> mmap (replicate (length spec) ro_alpha_round);
      dg \<leftarrow> protocol_absorb_read;
      assert (to_nat dg \<le> maxDegree);
      fl \<leftarrow> ntimes ro_receive_composition_fri_commits
        (ceil_log (to_nat dg + 1));
      final \<leftarrow> protocol_absorb_read;
      ntimes (ro_verifier_query_round_program fr f_fl f_final as fl final)
        rounds
    })"

lemma hash_range_budget_ro_receive_fri_commits_with:
  assumes challenge: "hash_range_budget q receive_challenge"
  shows "hash_range_budget (1 + q)
    (ro_receive_fri_commits_with receive_challenge)"
proof -
  have cont:
    "\<And>r. hash_range_budget (q + 0)
      (receive_challenge \<bind> (\<lambda>b. return (b, r)))"
    by (rule hash_range_budget_bind)
      (rule challenge, rule hash_range_budget_return)
  have budget:
    "hash_range_budget (1 + (q + 0))
      (ro_receive_fri_commits_with receive_challenge)"
    unfolding ro_receive_fri_commits_with_def
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_protocol_absorb_read, rule cont)
  then show ?thesis by simp
qed

lemma hash_collision_budget_ro_receive_fri_commits_with:
  assumes challenge_range: "hash_range_budget q receive_challenge"
    and challenge_collision: "hash_collision_budget q receive_challenge"
  shows "hash_collision_budget (1 + q)
    (ro_receive_fri_commits_with receive_challenge)"
proof -
  have cont_range:
    "\<And>r. hash_range_budget (q + 0)
      (receive_challenge \<bind> (\<lambda>b. return (b, r)))"
    by (rule hash_range_budget_bind)
      (rule challenge_range, rule hash_range_budget_return)
  have cont_collision:
    "\<And>r. hash_collision_budget (q + 0)
      (receive_challenge \<bind> (\<lambda>b. return (b, r)))"
    by (rule hash_collision_budget_bind)
      (rule challenge_range, rule challenge_collision,
        rule hash_range_budget_return, rule hash_collision_budget_return)
  have budget:
    "hash_collision_budget (1 + (q + 0))
      (ro_receive_fri_commits_with receive_challenge)"
    unfolding ro_receive_fri_commits_with_def
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_protocol_absorb_read,
        rule hash_collision_budget_protocol_absorb_read,
        rule cont_range, rule cont_collision)
  then show ?thesis by simp
qed

lemma hash_target_program_ro_receive_fri_commits_with:
  assumes challenge: "hash_target_program B q receive_challenge"
  shows "hash_target_program B (1 + q)
    (ro_receive_fri_commits_with receive_challenge)"
proof -
  have cont:
    "\<And>r. hash_target_program B (q + 0)
      (receive_challenge \<bind> (\<lambda>b. return (b, r)))"
    by (rule hash_target_program_bind)
      (rule challenge, rule hash_target_program_return)
  have budget:
    "hash_target_program B (1 + (q + 0))
      (ro_receive_fri_commits_with receive_challenge)"
    unfolding ro_receive_fri_commits_with_def
    by (rule hash_target_program_bind)
      (rule hash_target_program_protocol_absorb_read, rule cont)
  then show ?thesis by simp
qed

lemma hash_range_budget_ro_receive_trace_fri_commits:
  "hash_range_budget (1 + 1) ro_receive_trace_fri_commits"
  using hash_range_budget_ro_receive_fri_commits_with
    [OF hash_range_budget_receive_trace_fri_challenge]
  unfolding ro_receive_trace_fri_commits_def by simp

lemma hash_collision_budget_ro_receive_trace_fri_commits:
  "hash_collision_budget (1 + 1) ro_receive_trace_fri_commits"
  using hash_collision_budget_ro_receive_fri_commits_with
    [OF hash_range_budget_receive_trace_fri_challenge
      hash_collision_budget_receive_trace_fri_challenge]
  unfolding ro_receive_trace_fri_commits_def by simp

lemma hash_target_program_ro_receive_trace_fri_commits:
  "hash_target_program B (1 + 1) ro_receive_trace_fri_commits"
  using hash_target_program_ro_receive_fri_commits_with
    [OF hash_target_program_receive_trace_fri_challenge, of B]
  unfolding ro_receive_trace_fri_commits_def by simp

lemma hash_range_budget_ro_receive_composition_fri_commits:
  "hash_range_budget (1 + 1) ro_receive_composition_fri_commits"
  using hash_range_budget_ro_receive_fri_commits_with
    [OF hash_range_budget_receive_composition_fri_challenge]
  unfolding ro_receive_composition_fri_commits_def by simp

lemma hash_collision_budget_ro_receive_composition_fri_commits:
  "hash_collision_budget (1 + 1) ro_receive_composition_fri_commits"
  using hash_collision_budget_ro_receive_fri_commits_with
    [OF hash_range_budget_receive_composition_fri_challenge
      hash_collision_budget_receive_composition_fri_challenge]
  unfolding ro_receive_composition_fri_commits_def by simp

lemma hash_target_program_ro_receive_composition_fri_commits:
  "hash_target_program B (1 + 1) ro_receive_composition_fri_commits"
  using hash_target_program_ro_receive_fri_commits_with
    [OF hash_target_program_receive_composition_fri_challenge, of B]
  unfolding ro_receive_composition_fri_commits_def by simp

definition ro_verifier_fri_layer_hash_budget :: nat
  where
    "ro_verifier_fri_layer_hash_budget =
      2 * verifier_fri_layer_hash_budget"

definition ro_verifier_query_decommit_hash_budget :: nat
  where
    "ro_verifier_query_decommit_hash_budget =
      2 * verifier_query_decommit_hash_budget"

definition ro_verifier_query_round_hash_budget :: nat
  where
    "ro_verifier_query_round_hash_budget =
      1 + ro_verifier_query_decommit_hash_budget +
        (ceil_log clength + ceil_log (maxDegree + 1)) *
          ro_verifier_fri_layer_hash_budget"

definition ro_verifier_header_hash_budget :: nat
  where
    "ro_verifier_header_hash_budget =
      4 + 2 * verifier_header_hash_budget"

definition ro_verifier_hash_query_budget :: nat
  where
    "ro_verifier_hash_query_budget =
      ro_verifier_header_hash_budget +
        rounds * ro_verifier_query_round_hash_budget"

lemma hash_range_budget_ntimes_ro_receive_trace_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_range_budget (N * (1 + 1))
    (ntimes ro_receive_trace_fri_commits n)"
proof -
  have exact: "hash_range_budget (n * (1 + 1))
    (ntimes ro_receive_trace_fri_commits n)"
    by (rule hash_range_budget_ntimes)
      (rule hash_range_budget_ro_receive_trace_fri_commits)
  have le: "n * (1 + 1) \<le> N * (1 + 1)"
    using assms by (simp add: mult_right_mono)
  show ?thesis by (rule hash_range_budget_mono[OF le exact])
qed

lemma hash_collision_budget_ntimes_ro_receive_trace_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_collision_budget (N * (1 + 1))
    (ntimes ro_receive_trace_fri_commits n)"
proof -
  have exact: "hash_collision_budget (n * (1 + 1))
    (ntimes ro_receive_trace_fri_commits n)"
    by (rule hash_collision_budget_ntimes)
      (rule hash_range_budget_ro_receive_trace_fri_commits,
       rule hash_collision_budget_ro_receive_trace_fri_commits)
  have le: "n * (1 + 1) \<le> N * (1 + 1)"
    using assms by (simp add: mult_right_mono)
  show ?thesis by (rule hash_collision_budget_mono[OF le exact])
qed

lemma hash_target_program_ntimes_ro_receive_trace_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_target_program B (N * (1 + 1))
    (ntimes ro_receive_trace_fri_commits n)"
proof -
  have exact: "hash_target_program B (n * (1 + 1))
    (ntimes ro_receive_trace_fri_commits n)"
    by (rule hash_target_program_ntimes)
      (rule hash_target_program_ro_receive_trace_fri_commits)
  have le: "n * (1 + 1) \<le> N * (1 + 1)"
    using assms by (simp add: mult_right_mono)
  show ?thesis by (rule hash_target_program_mono[OF le exact])
qed

lemma hash_range_budget_ntimes_ro_receive_composition_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_range_budget (N * (1 + 1))
    (ntimes ro_receive_composition_fri_commits n)"
proof -
  have exact: "hash_range_budget (n * (1 + 1))
    (ntimes ro_receive_composition_fri_commits n)"
    by (rule hash_range_budget_ntimes)
      (rule hash_range_budget_ro_receive_composition_fri_commits)
  have le: "n * (1 + 1) \<le> N * (1 + 1)"
    using assms by (simp add: mult_right_mono)
  show ?thesis by (rule hash_range_budget_mono[OF le exact])
qed

lemma hash_collision_budget_ntimes_ro_receive_composition_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_collision_budget (N * (1 + 1))
    (ntimes ro_receive_composition_fri_commits n)"
proof -
  have exact: "hash_collision_budget (n * (1 + 1))
    (ntimes ro_receive_composition_fri_commits n)"
    by (rule hash_collision_budget_ntimes)
      (rule hash_range_budget_ro_receive_composition_fri_commits,
       rule hash_collision_budget_ro_receive_composition_fri_commits)
  have le: "n * (1 + 1) \<le> N * (1 + 1)"
    using assms by (simp add: mult_right_mono)
  show ?thesis by (rule hash_collision_budget_mono[OF le exact])
qed

lemma hash_target_program_ntimes_ro_receive_composition_fri_commits_bound:
  assumes "n \<le> N"
  shows "hash_target_program B (N * (1 + 1))
    (ntimes ro_receive_composition_fri_commits n)"
proof -
  have exact: "hash_target_program B (n * (1 + 1))
    (ntimes ro_receive_composition_fri_commits n)"
    by (rule hash_target_program_ntimes)
      (rule hash_target_program_ro_receive_composition_fri_commits)
  have le: "n * (1 + 1) \<le> N * (1 + 1)"
    using assms by (simp add: mult_right_mono)
  show ?thesis by (rule hash_target_program_mono[OF le exact])
qed

lemma hash_range_budget_ro_alpha_round:
  "hash_range_budget (1 + 1) ro_alpha_round"
proof -
  have assert_return:
    "hash_range_budget (0 + 0)
      (assert (a0 = a1) \<bind> (\<lambda>_. return a1) ::
        ('f, 'f protocol_channel) state_monad)" for a0 a1
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_assert, rule hash_range_budget_return)
  have after_absorb:
    "hash_range_budget (1 + (0 + 0))
      (protocol_absorb_read \<bind>
        (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, 'f protocol_channel) state_monad)" for a0
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_protocol_absorb_read, rule assert_return)
  have whole:
    "hash_range_budget (1 + (1 + (0 + 0)))
      (receive_alpha_challenge \<bind>
        (\<lambda>a0. protocol_absorb_read \<bind>
          (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1))) ::
        ('f, 'f protocol_channel) state_monad)"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_receive_alpha_challenge, rule after_absorb)
  then show ?thesis
    unfolding ro_alpha_round_def by simp
qed

lemma hash_collision_budget_ro_alpha_round:
  "hash_collision_budget (1 + 1) ro_alpha_round"
proof -
  have assert_return_range:
    "hash_range_budget (0 + 0)
      (assert (a0 = a1) \<bind> (\<lambda>_. return a1) ::
        ('f, 'f protocol_channel) state_monad)" for a0 a1
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_assert, rule hash_range_budget_return)
  have assert_return_collision:
    "hash_collision_budget (0 + 0)
      (assert (a0 = a1) \<bind> (\<lambda>_. return a1) ::
        ('f, 'f protocol_channel) state_monad)" for a0 a1
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_assert, rule hash_collision_budget_assert,
        rule hash_range_budget_return, rule hash_collision_budget_return)
  have after_absorb_range:
    "hash_range_budget (1 + (0 + 0))
      (protocol_absorb_read \<bind>
        (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, 'f protocol_channel) state_monad)" for a0
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_protocol_absorb_read, rule assert_return_range)
  have after_absorb_collision:
    "hash_collision_budget (1 + (0 + 0))
      (protocol_absorb_read \<bind>
        (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, 'f protocol_channel) state_monad)" for a0
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_protocol_absorb_read,
        rule hash_collision_budget_protocol_absorb_read,
        rule assert_return_range, rule assert_return_collision)
  have whole:
    "hash_collision_budget (1 + (1 + (0 + 0)))
      (receive_alpha_challenge \<bind>
        (\<lambda>a0. protocol_absorb_read \<bind>
          (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1))) ::
        ('f, 'f protocol_channel) state_monad)"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_receive_alpha_challenge,
        rule hash_collision_budget_receive_alpha_challenge,
        rule after_absorb_range, rule after_absorb_collision)
  then show ?thesis
    unfolding ro_alpha_round_def by simp
qed

lemma hash_target_program_ro_alpha_round:
  "hash_target_program B (1 + 1) ro_alpha_round"
proof -
  have assert_return:
    "hash_target_program B (0 + 0)
      (assert (a0 = a1) \<bind> (\<lambda>_. return a1) ::
        ('f, 'f protocol_channel) state_monad)" for a0 a1
    by (rule hash_target_program_bind)
      (rule hash_target_program_assert, rule hash_target_program_return)
  have after_absorb:
    "hash_target_program B (1 + (0 + 0))
      (protocol_absorb_read \<bind>
        (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, 'f protocol_channel) state_monad)" for a0
    by (rule hash_target_program_bind)
      (rule hash_target_program_protocol_absorb_read, rule assert_return)
  have whole:
    "hash_target_program B (1 + (1 + (0 + 0)))
      (receive_alpha_challenge \<bind>
        (\<lambda>a0. protocol_absorb_read \<bind>
          (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1))) ::
        ('f, 'f protocol_channel) state_monad)"
    by (rule hash_target_program_bind)
      (rule hash_target_program_receive_alpha_challenge, rule after_absorb)
  then show ?thesis
    unfolding ro_alpha_round_def by simp
qed

lemma ntimes_outcome_length:
  assumes "Some (xs, t) \<in> set_dist (execute (ntimes m n) s)"
  shows "length xs = n"
  using assms
proof (induction n arbitrary: s xs t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain x s1 ys where
    head: "Some (x, s1) \<in> set_dist (execute m s)"
    and tail: "Some (ys, t) \<in> set_dist (execute (ntimes m n) s1)"
    and xs_eq: "xs = x # ys"
    by (auto elim!: set_dist_bindE)
  have "length ys = n"
    by (rule Suc.IH[OF tail])
  then show ?case
    unfolding xs_eq by simp
qed

lemma hash_range_budget_ntimes_protocol_absorb_read_bind:
  fixes k :: "'f list \<Rightarrow> ('y, 'f protocol_channel) state_monad"
  assumes k: "\<And>xs. length xs = n \<Longrightarrow> hash_range_budget b (k xs)"
  shows "hash_range_budget (n + b)
    ((ntimes protocol_absorb_read n :: ('f list, 'f protocol_channel) state_monad) \<bind> k)"
proof -
  have reads:
    "hash_range_budget (n * 1)
      (ntimes protocol_absorb_read n ::
        ('f list, 'f protocol_channel) state_monad)"
    by (rule hash_range_budget_ntimes)
      (rule hash_range_budget_protocol_absorb_read)
  have "hash_range_budget (n * 1 + b)
      ((ntimes protocol_absorb_read n ::
        ('f list, 'f protocol_channel) state_monad) \<bind> k)"
  proof (rule hash_range_budget_bind_on_outcomes[OF reads])
    fix s xs t
    assume out:
      "Some (xs, t) \<in>
        set_dist (execute
          (ntimes protocol_absorb_read n ::
            ('f list, 'f protocol_channel) state_monad) s)"
    show "hash_range_budget b (k xs)"
      by (rule k) (rule ntimes_outcome_length[OF out])
  qed
  then show ?thesis by simp
qed

lemma hash_collision_budget_ntimes_protocol_absorb_read_bind:
  fixes k :: "'f list \<Rightarrow> ('y, 'f protocol_channel) state_monad"
  assumes range_k: "\<And>xs. length xs = n \<Longrightarrow> hash_range_budget b (k xs)"
    and collision_k: "\<And>xs. length xs = n \<Longrightarrow> hash_collision_budget b (k xs)"
  shows "hash_collision_budget (n + b)
    ((ntimes protocol_absorb_read n :: ('f list, 'f protocol_channel) state_monad) \<bind> k)"
proof -
  have reads_range:
    "hash_range_budget (n * 1)
      (ntimes protocol_absorb_read n ::
        ('f list, 'f protocol_channel) state_monad)"
    by (rule hash_range_budget_ntimes)
      (rule hash_range_budget_protocol_absorb_read)
  have reads_collision:
    "hash_collision_budget (n * 1)
      (ntimes protocol_absorb_read n ::
        ('f list, 'f protocol_channel) state_monad)"
    by (rule hash_collision_budget_ntimes)
      (rule hash_range_budget_protocol_absorb_read,
        rule hash_collision_budget_protocol_absorb_read)
  have "hash_collision_budget (n * 1 + b)
      ((ntimes protocol_absorb_read n ::
        ('f list, 'f protocol_channel) state_monad) \<bind> k)"
  proof (rule hash_collision_budget_bind_on_outcomes
      [OF reads_range reads_collision])
    fix s xs t
    assume out:
      "Some (xs, t) \<in>
        set_dist (execute
          (ntimes protocol_absorb_read n ::
            ('f list, 'f protocol_channel) state_monad) s)"
    have len: "length xs = n"
      by (rule ntimes_outcome_length[OF out])
    show "hash_range_budget b (k xs)"
      by (rule range_k[OF len])
    show "hash_collision_budget b (k xs)"
      by (rule collision_k[OF len])
  qed
  then show ?thesis by simp
qed

lemma hash_target_program_ntimes_protocol_absorb_read_bind:
  fixes k :: "'f list \<Rightarrow> ('y, 'f protocol_channel) state_monad"
  assumes k: "\<And>xs. length xs = n \<Longrightarrow> hash_target_program B b (k xs)"
  shows "hash_target_program B (n + b)
    ((ntimes protocol_absorb_read n :: ('f list, 'f protocol_channel) state_monad) \<bind> k)"
proof -
  have reads:
    "hash_target_program B (n * 1)
      (ntimes protocol_absorb_read n ::
        ('f list, 'f protocol_channel) state_monad)"
    by (rule hash_target_program_ntimes)
      (rule hash_target_program_protocol_absorb_read)
  have "hash_target_program B (n * 1 + b)
      ((ntimes protocol_absorb_read n ::
        ('f list, 'f protocol_channel) state_monad) \<bind> k)"
  proof (rule hash_target_program_bind_on_outcomes[OF reads])
    fix s xs t
    assume out:
      "Some (xs, t) \<in>
        set_dist (execute
          (ntimes protocol_absorb_read n ::
            ('f list, 'f protocol_channel) state_monad) s)"
    show "hash_target_program B b (k xs)"
      by (rule k) (rule ntimes_outcome_length[OF out])
  qed
  then show ?thesis by simp
qed

lemma hash_range_budget_ro_query_decommitment_step:
  "hash_range_budget (2 * Suc (floor_log (scale * clength)))
    (ro_query_decommitment_step fr i)"
proof -
  let ?len = "scale * clength"
  let ?L = "floor_log ?len"
  have path_tail:
    "hash_range_budget (Suc ?L)
      ((check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
    if path_len: "length path = ?L" for qh path
  proof -
    have exact:
      "hash_range_budget (Suc (length path))
        ((check_authentication_path ?len i qh path ::
            ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (rule hash_range_budget_check_authentication_path_assert_return)
    then show ?thesis
      using path_len by simp
  qed
  have after_path:
    "hash_range_budget (?L + Suc ?L)
      ((ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))" for qh
    by (rule hash_range_budget_ntimes_protocol_absorb_read_bind)
      (rule path_tail)
  have whole:
    "hash_range_budget (1 + (?L + Suc ?L))
      (protocol_absorb_read \<bind>
        (\<lambda>qh. (ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))) ::
        ('f, 'f protocol_channel) state_monad)"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_protocol_absorb_read, rule after_path)
  have budget_eq: "1 + (?L + Suc ?L) = 2 * Suc ?L"
    by simp
  have whole':
    "hash_range_budget (2 * Suc ?L)
      (protocol_absorb_read \<bind>
        (\<lambda>qh. (ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))) ::
        ('f, 'f protocol_channel) state_monad)"
    using whole unfolding budget_eq .
  show ?thesis
    using whole' unfolding ro_query_decommitment_step_def
    by (simp add: Let_def mult.commute)

qed

lemma hash_collision_budget_ro_query_decommitment_step:
  "hash_collision_budget (2 * Suc (floor_log (scale * clength)))
    (ro_query_decommitment_step fr i)"
proof -
  let ?len = "scale * clength"
  let ?L = "floor_log ?len"
  have path_tail_range:
    "hash_range_budget (Suc ?L)
      ((check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
    if path_len: "length path = ?L" for qh path
  proof -
    have exact:
      "hash_range_budget (Suc (length path))
        ((check_authentication_path ?len i qh path ::
            ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (rule hash_range_budget_check_authentication_path_assert_return)
    then show ?thesis
      using path_len by simp
  qed
  have path_tail_collision:
    "hash_collision_budget (Suc ?L)
      ((check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
    if path_len: "length path = ?L" for qh path
  proof -
    have exact:
      "hash_collision_budget (Suc (length path))
        ((check_authentication_path ?len i qh path ::
            ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (rule hash_collision_budget_check_authentication_path_assert_return)
    then show ?thesis
      using path_len by simp
  qed
  have after_path_range:
    "hash_range_budget (?L + Suc ?L)
      ((ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))" for qh
    by (rule hash_range_budget_ntimes_protocol_absorb_read_bind)
      (rule path_tail_range)
  have after_path_collision:
    "hash_collision_budget (?L + Suc ?L)
      ((ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))" for qh
  proof (rule hash_collision_budget_ntimes_protocol_absorb_read_bind)
    fix path :: "'f list"
    assume path_len: "length path = ?L"
    show "hash_range_budget (Suc ?L)
      ((check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (rule path_tail_range[OF path_len])
    show "hash_collision_budget (Suc ?L)
      ((check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (rule path_tail_collision[OF path_len])
  qed
  have whole:
    "hash_collision_budget (1 + (?L + Suc ?L))
      (protocol_absorb_read \<bind>
        (\<lambda>qh. (ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))) ::
        ('f, 'f protocol_channel) state_monad)"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_protocol_absorb_read,
        rule hash_collision_budget_protocol_absorb_read,
        rule after_path_range, rule after_path_collision)
  have budget_eq: "1 + (?L + Suc ?L) = 2 * Suc ?L"
    by simp
  have whole':
    "hash_collision_budget (2 * Suc ?L)
      (protocol_absorb_read \<bind>
        (\<lambda>qh. (ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))) ::
        ('f, 'f protocol_channel) state_monad)"
    using whole unfolding budget_eq .
  show ?thesis
    using whole' unfolding ro_query_decommitment_step_def
    by (simp add: Let_def mult.commute)

qed

lemma hash_target_program_ro_query_decommitment_step:
  "hash_target_program B (2 * Suc (floor_log (scale * clength)))
    (ro_query_decommitment_step fr i)"
proof -
  let ?len = "scale * clength"
  let ?L = "floor_log ?len"
  have path_tail:
    "hash_target_program B (Suc ?L)
      ((check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
    if path_len: "length path = ?L" for qh path
  proof -
    have exact:
      "hash_target_program B (Suc (length path))
        ((check_authentication_path ?len i qh path ::
            ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (rule hash_target_program_check_authentication_path_assert_return)
    then show ?thesis
      using path_len by simp
  qed
  have after_path:
    "hash_target_program B (?L + Suc ?L)
      ((ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))" for qh
    by (rule hash_target_program_ntimes_protocol_absorb_read_bind)
      (rule path_tail)
  have whole:
    "hash_target_program B (1 + (?L + Suc ?L))
      (protocol_absorb_read \<bind>
        (\<lambda>qh. (ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))) ::
        ('f, 'f protocol_channel) state_monad)"
    by (rule hash_target_program_bind)
      (rule hash_target_program_protocol_absorb_read, rule after_path)
  have budget_eq: "1 + (?L + Suc ?L) = 2 * Suc ?L"
    by simp
  have whole':
    "hash_target_program B (2 * Suc ?L)
      (protocol_absorb_read \<bind>
        (\<lambda>qh. (ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))) ::
        ('f, 'f protocol_channel) state_monad)"
    using whole unfolding budget_eq .
  show ?thesis
    using whole' unfolding ro_query_decommitment_step_def
    by (simp add: Let_def mult.commute)
qed

lemma hash_range_budget_ro_check_decommit_on_query:
  "hash_range_budget ro_verifier_query_decommit_hash_budget
    (mmap (ro_check_decommit_on_query fr idx))"
proof -
  let ?b = "2 * Suc (floor_log (scale * clength))"
  let ?steps =
    "map (ro_query_decommitment_step fr) (powers_scaled idx)"
  have step_budget:
    "\<And>m. m \<in> set ?steps \<Longrightarrow> hash_range_budget ?b m"
  proof -
    fix m
    assume "m \<in> set ?steps"
    then obtain j where m_eq: "m = ro_query_decommitment_step fr j"
      by auto
    show "hash_range_budget ?b m"
      unfolding m_eq by (rule hash_range_budget_ro_query_decommitment_step)
  qed
  have map_budget:
    "hash_range_budget (length ?steps * ?b) (mmap ?steps)"
    by (rule hash_range_budget_mmap) (rule step_budget)
  then show ?thesis
    unfolding ro_check_decommit_on_query_def
      ro_verifier_query_decommit_hash_budget_def
      verifier_query_decommit_hash_budget_def powers_scaled_def
    by (simp add: algebra_simps mult.commute)
qed

lemma hash_collision_budget_ro_check_decommit_on_query:
  "hash_collision_budget ro_verifier_query_decommit_hash_budget
    (mmap (ro_check_decommit_on_query fr idx))"
proof -
  let ?b = "2 * Suc (floor_log (scale * clength))"
  let ?steps =
    "map (ro_query_decommitment_step fr) (powers_scaled idx)"
  have step_range:
    "\<And>m. m \<in> set ?steps \<Longrightarrow> hash_range_budget ?b m"
  proof -
    fix m
    assume "m \<in> set ?steps"
    then obtain j where m_eq: "m = ro_query_decommitment_step fr j"
      by auto
    show "hash_range_budget ?b m"
      unfolding m_eq by (rule hash_range_budget_ro_query_decommitment_step)
  qed
  have step_collision:
    "\<And>m. m \<in> set ?steps \<Longrightarrow> hash_collision_budget ?b m"
  proof -
    fix m
    assume "m \<in> set ?steps"
    then obtain j where m_eq: "m = ro_query_decommitment_step fr j"
      by auto
    show "hash_collision_budget ?b m"
      unfolding m_eq by (rule hash_collision_budget_ro_query_decommitment_step)
  qed
  have map_budget:
    "hash_collision_budget (length ?steps * ?b) (mmap ?steps)"
  proof (rule hash_collision_budget_mmap)
    fix m
    assume m_in: "m \<in> set ?steps"
    show "hash_range_budget ?b m"
      by (rule step_range[OF m_in])
    show "hash_collision_budget ?b m"
      by (rule step_collision[OF m_in])
  qed
  then show ?thesis
    unfolding ro_check_decommit_on_query_def
      ro_verifier_query_decommit_hash_budget_def
      verifier_query_decommit_hash_budget_def powers_scaled_def
    by (simp add: algebra_simps mult.commute)
qed

lemma hash_target_program_ro_check_decommit_on_query:
  "hash_target_program B ro_verifier_query_decommit_hash_budget
    (mmap (ro_check_decommit_on_query fr idx))"
proof -
  let ?b = "2 * Suc (floor_log (scale * clength))"
  let ?steps =
    "map (ro_query_decommitment_step fr) (powers_scaled idx)"
  have step_budget:
    "\<And>m. m \<in> set ?steps \<Longrightarrow> hash_target_program B ?b m"
  proof -
    fix m
    assume "m \<in> set ?steps"
    then obtain j where m_eq: "m = ro_query_decommitment_step fr j"
      by auto
    show "hash_target_program B ?b m"
      unfolding m_eq by (rule hash_target_program_ro_query_decommitment_step)
  qed
  have map_budget:
    "hash_target_program B (length ?steps * ?b) (mmap ?steps)"
    by (rule hash_target_program_mmap) (rule step_budget)
  then show ?thesis
    unfolding ro_check_decommit_on_query_def
      ro_verifier_query_decommit_hash_budget_def
      verifier_query_decommit_hash_budget_def powers_scaled_def
    by (simp add: algebra_simps mult.commute)
qed

lemma hash_range_budget_ro_fri_layer_opening_step:
  assumes len_le: "floor_log len \<le> L"
  shows "hash_range_budget (2 * (Suc L + Suc L))
    (ro_fri_layer_opening_step (b, f) (i, x, len, pw))"
proof -
  let ?l = "floor_log len"
  let ?exact = "Suc ?l + Suc ?l"
  have finish:
    "hash_range_budget ?exact
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
    if xp_len: "length xp_path = ?l"
      and xn_len: "length xn_path = ?l"
    for xp xp_path xn xn_path
    by (rule hash_range_budget_fri_layer_opening_finish
        [OF xp_len xn_len])
  have after_xn_path:
    "hash_range_budget (?l + ?exact)
      ((ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
          xp xp_path xn xn_path))"
    if xp_len: "length xp_path = ?l" for xp xp_path xn
    by (rule hash_range_budget_ntimes_protocol_absorb_read_bind)
      (rule finish[OF xp_len])
  have after_xn:
    "hash_range_budget (1 + (?l + ?exact))
      (protocol_absorb_read \<bind>
        (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
            xp xp_path xn xn_path)) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    if xp_len: "length xp_path = ?l" for xp xp_path
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_protocol_absorb_read,
        rule after_xn_path[OF xp_len])
  have after_xp_path:
    "hash_range_budget (?l + (1 + (?l + ?exact)))
      ((ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>xp_path. protocol_absorb_read \<bind>
          (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
            ('f list, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
              xp xp_path xn xn_path))) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)" for xp
    by (rule hash_range_budget_ntimes_protocol_absorb_read_bind)
      (rule after_xn)
  have whole:
    "hash_range_budget (1 + (?l + (1 + (?l + ?exact))))
      (protocol_absorb_read \<bind>
        (\<lambda>xp. (ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xp_path. protocol_absorb_read \<bind>
            (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
              ('f list, 'f protocol_channel) state_monad) \<bind>
              (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
                xp xp_path xn xn_path)))) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_protocol_absorb_read, rule after_xp_path)
  have budget_eq:
    "1 + (?l + (1 + (?l + ?exact))) = 2 * ?exact"
    by simp
  have exact:
    "hash_range_budget (2 * ?exact)
      (ro_fri_layer_opening_step (b, f) (i, x, len, pw))"
    using whole unfolding ro_fri_layer_opening_step_def budget_eq
    by simp
  have le: "2 * ?exact \<le> 2 * (Suc L + Suc L)"
    using len_le by simp
  show ?thesis
    by (rule hash_range_budget_mono[OF le exact])
qed

lemma hash_collision_budget_ro_fri_layer_opening_step:
  assumes len_le: "floor_log len \<le> L"
  shows "hash_collision_budget (2 * (Suc L + Suc L))
    (ro_fri_layer_opening_step (b, f) (i, x, len, pw))"
proof -
  let ?l = "floor_log len"
  let ?exact = "Suc ?l + Suc ?l"
  have finish_range:
    "hash_range_budget ?exact
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
    if xp_len: "length xp_path = ?l"
      and xn_len: "length xn_path = ?l"
    for xp xp_path xn xn_path
    by (rule hash_range_budget_fri_layer_opening_finish
        [OF xp_len xn_len])
  have finish_collision:
    "hash_collision_budget ?exact
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
    if xp_len: "length xp_path = ?l"
      and xn_len: "length xn_path = ?l"
    for xp xp_path xn xn_path
    by (rule hash_collision_budget_fri_layer_opening_finish
        [OF xp_len xn_len])
  have after_xn_path_range:
    "hash_range_budget (?l + ?exact)
      ((ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
          xp xp_path xn xn_path))"
    if xp_len: "length xp_path = ?l" for xp xp_path xn
    by (rule hash_range_budget_ntimes_protocol_absorb_read_bind)
      (rule finish_range[OF xp_len])
  have after_xn_path_collision:
    "hash_collision_budget (?l + ?exact)
      ((ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
          xp xp_path xn xn_path))"
    if xp_len: "length xp_path = ?l" for xp xp_path xn
  proof (rule hash_collision_budget_ntimes_protocol_absorb_read_bind)
    fix xn_path :: "'f list"
    assume xn_len: "length xn_path = ?l"
    show "hash_range_budget ?exact
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
      by (rule finish_range[OF xp_len xn_len])
    show "hash_collision_budget ?exact
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
      by (rule finish_collision[OF xp_len xn_len])
  qed
  have after_xn_range:
    "hash_range_budget (1 + (?l + ?exact))
      (protocol_absorb_read \<bind>
        (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
            xp xp_path xn xn_path)) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    if xp_len: "length xp_path = ?l" for xp xp_path
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_protocol_absorb_read,
        rule after_xn_path_range[OF xp_len])
  have after_xn_collision:
    "hash_collision_budget (1 + (?l + ?exact))
      (protocol_absorb_read \<bind>
        (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
            xp xp_path xn xn_path)) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    if xp_len: "length xp_path = ?l" for xp xp_path
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_protocol_absorb_read,
        rule hash_collision_budget_protocol_absorb_read,
        rule after_xn_path_range[OF xp_len],
        rule after_xn_path_collision[OF xp_len])
  have after_xp_path_range:
    "hash_range_budget (?l + (1 + (?l + ?exact)))
      ((ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>xp_path. protocol_absorb_read \<bind>
          (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
            ('f list, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
              xp xp_path xn xn_path))) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)" for xp
    by (rule hash_range_budget_ntimes_protocol_absorb_read_bind)
      (rule after_xn_range)
  have after_xp_path_collision:
    "hash_collision_budget (?l + (1 + (?l + ?exact)))
      ((ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>xp_path. protocol_absorb_read \<bind>
          (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
            ('f list, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
              xp xp_path xn xn_path))) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)" for xp
  proof (rule hash_collision_budget_ntimes_protocol_absorb_read_bind)
    fix xp_path :: "'f list"
    assume xp_len: "length xp_path = ?l"
    show "hash_range_budget (1 + (?l + ?exact))
      (protocol_absorb_read \<bind>
        (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
          fri_layer_opening_finish b f i x len pw xp xp_path xn) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      by (rule after_xn_range[OF xp_len])
    show "hash_collision_budget (1 + (?l + ?exact))
      (protocol_absorb_read \<bind>
        (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
          fri_layer_opening_finish b f i x len pw xp xp_path xn) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      by (rule after_xn_collision[OF xp_len])
  qed
  have whole_range:
    "hash_range_budget (1 + (?l + (1 + (?l + ?exact))))
      (protocol_absorb_read \<bind>
        (\<lambda>xp. (ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xp_path. protocol_absorb_read \<bind>
            (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
              ('f list, 'f protocol_channel) state_monad) \<bind>
              (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
                xp xp_path xn xn_path)))) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_protocol_absorb_read, rule after_xp_path_range)
  have whole_collision:
    "hash_collision_budget (1 + (?l + (1 + (?l + ?exact))))
      (protocol_absorb_read \<bind>
        (\<lambda>xp. (ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xp_path. protocol_absorb_read \<bind>
            (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
              ('f list, 'f protocol_channel) state_monad) \<bind>
              (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
                xp xp_path xn xn_path)))) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_protocol_absorb_read,
        rule hash_collision_budget_protocol_absorb_read,
        rule after_xp_path_range, rule after_xp_path_collision)
  have budget_eq:
    "1 + (?l + (1 + (?l + ?exact))) = 2 * ?exact"
    by simp
  have exact:
    "hash_collision_budget (2 * ?exact)
      (ro_fri_layer_opening_step (b, f) (i, x, len, pw))"
    using whole_collision unfolding ro_fri_layer_opening_step_def budget_eq
    by simp
  have le: "2 * ?exact \<le> 2 * (Suc L + Suc L)"
    using len_le by simp
  show ?thesis
    by (rule hash_collision_budget_mono[OF le exact])
qed

lemma hash_target_program_mfold_invariant:
  fixes steps :: "('x \<Rightarrow> ('x, ('f, 'a) protocol_channel_scheme) state_monad) list"
  assumes init: "I x"
    and step_budget:
      "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        hash_target_program B n (step y)"
    and step_inv:
      "\<And>step y z s t. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        Some (z, t) \<in> set_dist (execute (step y) s) \<Longrightarrow> I z"
  shows "hash_target_program B (length steps * n) (mfold x steps)"
  using init step_budget step_inv
proof (induction steps arbitrary: x)
  case Nil
  then show ?case
    by (simp add: hash_target_program_return)
next
  case (Cons step steps)
  have Ix: "I x"
    using Cons.prems by simp
  have head: "hash_target_program B n (step x)"
    by (rule Cons.prems(2)) (use Ix in auto)
  have tail:
    "hash_target_program B (length steps * n) (mfold y steps)"
    if out: "Some (y, t) \<in> set_dist (execute (step x) s)"
    for s y t
  proof (rule Cons.IH)
    show "I y"
    proof -
      have mem: "step \<in> set (step # steps)"
        by simp
      have inv:
        "\<And>z s t. Some (z, t) \<in> set_dist (execute (step x) s) \<Longrightarrow> I z"
        by (rule Cons.prems(3)[OF mem Ix])
      show ?thesis
        by (rule inv[OF out])
    qed
    show "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
      hash_target_program B n (step y)"
      by (rule Cons.prems(2)) simp_all
    show "\<And>step y z s t. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
      Some (z, t) \<in> set_dist (execute (step y) s) \<Longrightarrow> I z"
      by (rule Cons.prems(3)) simp_all
  qed
  have "hash_target_program B (n + length steps * n)
      (step x \<bind> (\<lambda>y. mfold y steps))"
    by (rule hash_target_program_bind_on_outcomes[OF head]) (rule tail)
  then show ?case
    by simp
qed

lemma ro_fri_layer_opening_step_outcome_len:
  assumes out:
    "Some (z, t) \<in>
      set_dist (execute (ro_fri_layer_opening_step (b, f) (i, x, len, pw)) s)"
  shows "case z of (j, y, len', pw') \<Rightarrow> len' = len div 2"
  using out
  unfolding ro_fri_layer_opening_step_def fri_layer_opening_finish_def
  by (auto elim!: set_dist_bindE split: prod.splits)

lemma hash_target_program_ro_fri_layer_opening_step:
  assumes len_le: "floor_log len \<le> L"
  shows "hash_target_program B (2 * (Suc L + Suc L))
    (ro_fri_layer_opening_step (b, f) (i, x, len, pw))"
proof -
  let ?l = "floor_log len"
  let ?exact = "Suc ?l + Suc ?l"
  have finish:
    "hash_target_program B ?exact
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
    if xp_len: "length xp_path = ?l"
      and xn_len: "length xn_path = ?l"
    for xp xp_path xn xn_path
    by (rule hash_target_program_fri_layer_opening_finish
        [OF xp_len xn_len])
  have after_xn_path:
    "hash_target_program B (?l + ?exact)
      ((ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
          xp xp_path xn xn_path))"
    if xp_len: "length xp_path = ?l" for xp xp_path xn
    by (rule hash_target_program_ntimes_protocol_absorb_read_bind)
      (rule finish[OF xp_len])
  have after_xn:
    "hash_target_program B (1 + (?l + ?exact))
      (protocol_absorb_read \<bind>
        (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
            xp xp_path xn xn_path)) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    if xp_len: "length xp_path = ?l" for xp xp_path
    by (rule hash_target_program_bind)
      (rule hash_target_program_protocol_absorb_read,
        rule after_xn_path[OF xp_len])
  have after_xp_path:
    "hash_target_program B (?l + (1 + (?l + ?exact)))
      ((ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>xp_path. protocol_absorb_read \<bind>
          (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
            ('f list, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
              xp xp_path xn xn_path))) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)" for xp
    by (rule hash_target_program_ntimes_protocol_absorb_read_bind)
      (rule after_xn)
  have whole:
    "hash_target_program B (1 + (?l + (1 + (?l + ?exact))))
      (protocol_absorb_read \<bind>
        (\<lambda>xp. (ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xp_path. protocol_absorb_read \<bind>
            (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
              ('f list, 'f protocol_channel) state_monad) \<bind>
              (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
                xp xp_path xn xn_path)))) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    by (rule hash_target_program_bind)
      (rule hash_target_program_protocol_absorb_read, rule after_xp_path)
  have budget_eq:
    "1 + (?l + (1 + (?l + ?exact))) = 2 * ?exact"
    by simp
  have exact:
    "hash_target_program B (2 * ?exact)
      (ro_fri_layer_opening_step (b, f) (i, x, len, pw))"
    using whole unfolding ro_fri_layer_opening_step_def budget_eq
    by simp
  have le: "2 * ?exact \<le> 2 * (Suc L + Suc L)"
    using len_le by simp
  show ?thesis
    by (rule hash_target_program_mono[OF le exact])
qed

lemma ro_fri_layer_opening_step_preserves_floor_log_bound:
  assumes len_bound: "floor_log len \<le> L"
    and out:
      "Some (z, t) \<in>
        set_dist (execute (ro_fri_layer_opening_step (b, f) (i, x, len, pw)) s)"
  shows "case z of (j, y, len', pw') \<Rightarrow> floor_log len' \<le> L"
proof -
  have len_eq: "case z of (j, y, len', pw') \<Rightarrow> len' = len div 2"
    by (rule ro_fri_layer_opening_step_outcome_len[OF out])
  have next_bound: "floor_log (len div 2) \<le> L"
    using floor_log_div2_le_self[of len] len_bound by linarith
  show ?thesis
    using len_eq next_bound by (cases z) auto
qed



definition ro_checked_staged_security_experiment
  :: "'f staged_adversary \<Rightarrow>
      (unit list, 'f protocol_channel) state_monad"
  where
    "ro_checked_staged_security_experiment A =
      ro_checked_staged_transcript_program A \<bind> (\<lambda>data.
        get \<bind> (\<lambda>s.
          put
            (verifier_state_from_adversary s
              (staged_proof_transcript data)) \<bind>
            (\<lambda>_. verify_monad)))"

definition ro_checked_staged_security_experiment_with_data
  :: "'f staged_adversary \<Rightarrow>
      ('f staged_proof_data \<times> unit list, 'f protocol_channel) state_monad"
  where
    "ro_checked_staged_security_experiment_with_data A =
      ro_checked_staged_transcript_program A \<bind> (\<lambda>data.
        get \<bind> (\<lambda>s.
          put
            (verifier_state_from_adversary s
              (staged_proof_transcript data)) \<bind>
            (\<lambda>_. verify_monad \<bind> (\<lambda>result. return (data, result)))))"

definition ro_checked_staged_security_experiment_with_data_state
  :: "'f staged_adversary \<Rightarrow>
      (('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list,
        'f protocol_channel) state_monad"
  where
    "ro_checked_staged_security_experiment_with_data_state A =
      ro_checked_staged_transcript_program A \<bind> (\<lambda>data.
        get \<bind> (\<lambda>s.
          put
            (verifier_state_from_adversary s
              (staged_proof_transcript data)) \<bind>
            (\<lambda>_.
              verify_monad \<bind>
                (\<lambda>result. return ((data, s), result)))))"

definition ro_absorb_checked_staged_security_experiment
  :: "'f staged_adversary \<Rightarrow>
      (unit list, 'f protocol_channel) state_monad"
  where
    "ro_absorb_checked_staged_security_experiment A =
      ro_checked_staged_transcript_program A \<bind> (\<lambda>data.
        get \<bind> (\<lambda>s.
          put
            (verifier_state_from_adversary s
              (staged_proof_transcript data)) \<bind>
            (\<lambda>_. ro_verify_monad)))"

definition ro_absorb_checked_staged_security_experiment_with_data
  :: "'f staged_adversary \<Rightarrow>
      ('f staged_proof_data \<times> unit list, 'f protocol_channel) state_monad"
  where
    "ro_absorb_checked_staged_security_experiment_with_data A =
      ro_checked_staged_transcript_program A \<bind> (\<lambda>data.
        get \<bind> (\<lambda>s.
          put
            (verifier_state_from_adversary s
              (staged_proof_transcript data)) \<bind>
            (\<lambda>_. ro_verify_monad \<bind> (\<lambda>result. return (data, result)))))"

definition ro_absorb_checked_staged_security_experiment_with_data_state
  :: "'f staged_adversary \<Rightarrow>
      (('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list,
        'f protocol_channel) state_monad"
  where
    "ro_absorb_checked_staged_security_experiment_with_data_state A =
      ro_checked_staged_transcript_program A \<bind> (\<lambda>data.
        get \<bind> (\<lambda>s.
          put
            (verifier_state_from_adversary s
              (staged_proof_transcript data)) \<bind>
            (\<lambda>_.
              ro_verify_monad \<bind>
                (\<lambda>result. return ((data, s), result)))))"

lemma ro_checked_staged_security_experiment_projection:
  "ro_checked_staged_security_experiment_with_data A \<bind>
    (\<lambda>x. return (snd x)) =
    ro_checked_staged_security_experiment A"
  unfolding ro_checked_staged_security_experiment_with_data_def
    ro_checked_staged_security_experiment_def
  by (simp add: sm_bind_assoc split: prod.splits)

lemma ro_checked_staged_security_experiment_with_data_state_projection:
  "ro_checked_staged_security_experiment_with_data_state A \<bind>
    (\<lambda>x. return (snd x)) =
    ro_checked_staged_security_experiment A"
  unfolding ro_checked_staged_security_experiment_with_data_state_def
    ro_checked_staged_security_experiment_def
  by (simp add: sm_bind_assoc split: prod.splits)

lemma ro_checked_staged_security_experiment_with_data_state_projection_to_data:
  "ro_checked_staged_security_experiment_with_data_state A \<bind>
    (\<lambda>x. case x of ((data, _), result) \<Rightarrow>
      return (data, result)) =
    ro_checked_staged_security_experiment_with_data A"
  unfolding ro_checked_staged_security_experiment_with_data_state_def
    ro_checked_staged_security_experiment_with_data_def
  by (simp add: sm_bind_assoc split: prod.splits)

lemma ro_absorb_checked_staged_security_experiment_projection:
  "ro_absorb_checked_staged_security_experiment_with_data A \<bind>
    (\<lambda>x. return (snd x)) =
    ro_absorb_checked_staged_security_experiment A"
  unfolding ro_absorb_checked_staged_security_experiment_with_data_def
    ro_absorb_checked_staged_security_experiment_def
  by (simp add: sm_bind_assoc split: prod.splits)

lemma ro_absorb_checked_staged_security_experiment_with_data_state_projection:
  "ro_absorb_checked_staged_security_experiment_with_data_state A \<bind>
    (\<lambda>x. return (snd x)) =
    ro_absorb_checked_staged_security_experiment A"
  unfolding ro_absorb_checked_staged_security_experiment_with_data_state_def
    ro_absorb_checked_staged_security_experiment_def
  by (simp add: sm_bind_assoc split: prod.splits)

lemma ro_absorb_checked_staged_security_experiment_with_data_state_projection_to_data:
  "ro_absorb_checked_staged_security_experiment_with_data_state A \<bind>
    (\<lambda>x. case x of ((data, _), result) \<Rightarrow>
      return (data, result)) =
    ro_absorb_checked_staged_security_experiment_with_data A"
  unfolding ro_absorb_checked_staged_security_experiment_with_data_state_def
    ro_absorb_checked_staged_security_experiment_with_data_def
  by (simp add: sm_bind_assoc split: prod.splits)

lemma ro_checked_staged_security_experiment_acceptance_with_data:
  "wp_event (ro_checked_staged_security_experiment A) accepted
      adversary_initial_state =
    wp_event (ro_checked_staged_security_experiment_with_data A) accepted
      adversary_initial_state"
proof -
  have proj:
    "ro_checked_staged_security_experiment A =
      ro_checked_staged_security_experiment_with_data A \<bind>
        (\<lambda>x. return (snd x))"
    using ro_checked_staged_security_experiment_projection by simp
  show ?thesis
    unfolding proj
    by (subst wp_event_bind_return_map[where f=snd])
      (unfold wp_event_def accepted_def,
       rule arg_cong[where
        f="\<lambda>Q. wp (ro_checked_staged_security_experiment_with_data A) Q
          adversary_initial_state"],
       rule ext, simp split: option.splits prod.splits)
qed

lemma ro_checked_staged_security_experiment_acceptance_with_data_state:
  "wp_event (ro_checked_staged_security_experiment A) accepted
      adversary_initial_state =
    wp_event (ro_checked_staged_security_experiment_with_data_state A) accepted
      adversary_initial_state"
proof -
  have proj:
    "ro_checked_staged_security_experiment A =
      ro_checked_staged_security_experiment_with_data_state A \<bind>
        (\<lambda>x. return (snd x))"
    using ro_checked_staged_security_experiment_with_data_state_projection
    by simp
  show ?thesis
    unfolding proj
    by (subst wp_event_bind_return_map[where f=snd])
      (unfold wp_event_def accepted_def,
       rule arg_cong[where
        f="\<lambda>Q. wp (ro_checked_staged_security_experiment_with_data_state A) Q
          adversary_initial_state"],
       rule ext, simp split: option.splits prod.splits)
qed

lemma ro_checked_staged_security_experiment_with_data_event_from_data_state:
  "wp_event (ro_checked_staged_security_experiment_with_data A) P
      adversary_initial_state =
    wp_event (ro_checked_staged_security_experiment_with_data_state A)
      (\<lambda>out. case out of None \<Rightarrow> P None
        | Some (((data, _), result), t) \<Rightarrow> P (Some ((data, result), t)))
      adversary_initial_state"
proof -
  have proj:
    "ro_checked_staged_security_experiment_with_data A =
      ro_checked_staged_security_experiment_with_data_state A \<bind>
        (\<lambda>x. case x of ((data, _), result) \<Rightarrow>
          return (data, result))"
    using ro_checked_staged_security_experiment_with_data_state_projection_to_data
    by simp
  show ?thesis
    unfolding proj wp_event_def
    apply (subst wp_bind)
    apply (rule arg_cong[where
      f="\<lambda>Q. wp (ro_checked_staged_security_experiment_with_data_state A) Q
        adversary_initial_state"])
    apply (rule ext)
    apply (simp add: wp_return split: option.splits prod.splits)
    done
qed

lemma ro_absorb_checked_staged_security_experiment_acceptance_with_data:
  "wp_event (ro_absorb_checked_staged_security_experiment A) accepted
      adversary_initial_state =
    wp_event (ro_absorb_checked_staged_security_experiment_with_data A) accepted
      adversary_initial_state"
proof -
  have proj:
    "ro_absorb_checked_staged_security_experiment A =
      ro_absorb_checked_staged_security_experiment_with_data A \<bind>
        (\<lambda>x. return (snd x))"
    using ro_absorb_checked_staged_security_experiment_projection by simp
  show ?thesis
    unfolding proj
    by (subst wp_event_bind_return_map[where f=snd])
      (unfold wp_event_def accepted_def,
       rule arg_cong[where
        f="\<lambda>Q. wp (ro_absorb_checked_staged_security_experiment_with_data A) Q
          adversary_initial_state"],
       rule ext, simp split: option.splits prod.splits)
qed

lemma ro_absorb_checked_staged_security_experiment_acceptance_with_data_state:
  "wp_event (ro_absorb_checked_staged_security_experiment A) accepted
      adversary_initial_state =
    wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A) accepted
      adversary_initial_state"
proof -
  have proj:
    "ro_absorb_checked_staged_security_experiment A =
      ro_absorb_checked_staged_security_experiment_with_data_state A \<bind>
        (\<lambda>x. return (snd x))"
    using ro_absorb_checked_staged_security_experiment_with_data_state_projection
    by simp
  show ?thesis
    unfolding proj
    by (subst wp_event_bind_return_map[where f=snd])
      (unfold wp_event_def accepted_def,
       rule arg_cong[where
        f="\<lambda>Q. wp (ro_absorb_checked_staged_security_experiment_with_data_state A) Q
          adversary_initial_state"],
       rule ext, simp split: option.splits prod.splits)
qed

lemma ro_absorb_checked_staged_security_experiment_with_data_event_from_data_state:
  "wp_event (ro_absorb_checked_staged_security_experiment_with_data A) P
      adversary_initial_state =
    wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
      (\<lambda>out. case out of None \<Rightarrow> P None
        | Some (((data, _), result), t) \<Rightarrow> P (Some ((data, result), t)))
      adversary_initial_state"
proof -
  have proj:
    "ro_absorb_checked_staged_security_experiment_with_data A =
      ro_absorb_checked_staged_security_experiment_with_data_state A \<bind>
        (\<lambda>x. case x of ((data, _), result) \<Rightarrow>
          return (data, result))"
    using ro_absorb_checked_staged_security_experiment_with_data_state_projection_to_data
    by simp
  show ?thesis
    unfolding proj wp_event_def
    apply (subst wp_bind)
    apply (rule arg_cong[where
      f="\<lambda>Q. wp (ro_absorb_checked_staged_security_experiment_with_data_state A) Q
        adversary_initial_state"])
    apply (rule ext)
    apply (simp add: wp_return split: option.splits prod.splits)
    done
qed

lemma ro_checked_staged_security_experiment_with_data_state_outcomeE:
  assumes
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_security_experiment_with_data_state A)
          initial_state)"
  obtains
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (ro_checked_staged_transcript_program A) initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
  using assms
  unfolding ro_checked_staged_security_experiment_with_data_state_def
  by (auto elim!: set_dist_bindE intro: that)

lemma ro_checked_staged_security_with_data_state_verifier_event_bound_from_cont:
  assumes no_none: "\<And>s. \<not> P s None"
    and cont_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (P
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
  shows
    "wp_event (ro_checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event P)
      adversary_initial_state \<le> C"
  unfolding ro_checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> staged_security_with_data_state_verifier_event P None"
    unfolding staged_security_with_data_state_verifier_event_def by simp
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (ro_checked_staged_transcript_program A)
          adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have cont_eq:
    "wp_event
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad \<bind>
            (\<lambda>result. return ((data, s), result)))))
      (staged_security_with_data_state_verifier_event P) attacker_state =
      wp_event verify_monad (P ?s) ?s"
    unfolding wp_event_def staged_security_with_data_state_verifier_event_def
    apply (simp add: wpsimps)
    apply (rule arg_cong[where f="\<lambda>Q. wp verify_monad Q ?s"])
    apply (rule ext)
    apply (simp add: no_none wp_return split: option.splits prod.splits)
    done
  show
    "wp_event
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad \<bind>
            (\<lambda>result. return ((data, s), result)))))
      (staged_security_with_data_state_verifier_event P) attacker_state \<le> C"
    unfolding cont_eq by (rule cont_bound[OF builder])
qed

lemma ro_absorb_checked_staged_security_experiment_with_data_state_outcomeE:
  assumes
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (ro_absorb_checked_staged_security_experiment_with_data_state A)
          initial_state)"
  obtains
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (ro_checked_staged_transcript_program A) initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute ro_verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
  using assms
  unfolding ro_absorb_checked_staged_security_experiment_with_data_state_def
  by (auto elim!: set_dist_bindE intro: that)

lemma ro_absorb_checked_staged_security_with_data_state_verifier_event_bound_from_cont:
  assumes no_none: "\<And>s. \<not> P s None"
    and cont_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
      wp_event ro_verify_monad
        (P
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
  shows
    "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event P)
      adversary_initial_state \<le> C"
  unfolding ro_absorb_checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> staged_security_with_data_state_verifier_event P None"
    unfolding staged_security_with_data_state_verifier_event_def by simp
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (ro_checked_staged_transcript_program A)
          adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have cont_eq:
    "wp_event
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. ro_verify_monad \<bind>
            (\<lambda>result. return ((data, s), result)))))
      (staged_security_with_data_state_verifier_event P) attacker_state =
      wp_event ro_verify_monad (P ?s) ?s"
    unfolding wp_event_def staged_security_with_data_state_verifier_event_def
    apply (simp add: wpsimps)
    apply (rule arg_cong[where f="\<lambda>Q. wp ro_verify_monad Q ?s"])
    apply (rule ext)
    apply (simp add: no_none wp_return split: option.splits prod.splits)
    done
  show
    "wp_event
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. ro_verify_monad \<bind>
            (\<lambda>result. return ((data, s), result)))))
      (staged_security_with_data_state_verifier_event P) attacker_state \<le> C"
    unfolding cont_eq by (rule cont_bound[OF builder])
qed

lemma ro_checked_staged_security_with_data_state_bound_from_data_cont:
  assumes none: "\<not> P None"
    and cont_bound:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (ro_checked_staged_transcript_program A)
              adversary_initial_state) \<Longrightarrow>
        wp_event verify_monad
          (\<lambda>out.
            P (case out of
                None \<Rightarrow> None
              | Some (result, final_state) \<Rightarrow>
                  Some (((data, attacker_state), result), final_state)))
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) \<le> C"
  shows
    "wp_event (ro_checked_staged_security_experiment_with_data_state A) P
      adversary_initial_state \<le> C"
  unfolding ro_checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> P None"
    by (rule none)
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (ro_checked_staged_transcript_program A)
          adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have cont_eq:
    "wp_event
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad \<bind>
            (\<lambda>result. return ((data, s), result)))))
      P attacker_state =
     wp_event verify_monad
      (\<lambda>out.
        P (case out of
            None \<Rightarrow> None
          | Some (result, final_state) \<Rightarrow>
              Some (((data, attacker_state), result), final_state)))
      ?s"
    unfolding wp_event_def
    apply (simp add: none wpsimps)
    apply (rule arg_cong[where f="\<lambda>Q. wp verify_monad Q ?s"])
    apply (rule ext)
    apply (rename_tac out)
    apply (case_tac out)
     apply (simp add: none)
    apply (rename_tac result_state)
    apply (case_tac result_state)
    by (simp add: wp_return)
  show
    "wp_event
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad \<bind>
            (\<lambda>result. return ((data, s), result)))))
      P attacker_state \<le> C"
    unfolding cont_eq by (rule cont_bound[OF builder])
qed

lemma ro_checked_staged_security_with_data_state_query_bad_verifier_event_bound:
  assumes query_bound:
    "wp_event (ro_checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le> C"
  shows
    "wp_event (ro_checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le> C"
proof -
  have "wp_event (ro_checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le>
    wp_event (ro_checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute
            (ro_checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and event:
      "staged_security_with_data_state_verifier_event query_bad out"
    show "staged_security_with_data_state_query_bad_hit out"
    proof (cases out)
      case None
      then show ?thesis
        using event unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      have verifier:
        "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
        using ro_checked_staged_security_experiment_with_data_state_outcomeE
          [OF support[unfolded out_eq]]
        by blast
      have bad: "query_bad ?s (Some (result, final_state))"
        using event
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
      show ?thesis
        unfolding out_eq staged_security_with_data_state_query_bad_hit_def
          Let_def
        using verifier bad by simp
    qed
  qed
  also have "... \<le> C"
    by (rule query_bound)
  finally show ?thesis .
qed

definition ro_checked_staged_adversary_acceptance_probability
  :: "'f staged_adversary \<Rightarrow> prob"
  where
    "ro_checked_staged_adversary_acceptance_probability A =
      wp_event (ro_checked_staged_security_experiment A)
        (\<lambda>out. \<not> Option.is_none out) adversary_initial_state"

definition ro_absorb_checked_staged_adversary_acceptance_probability
  :: "'f staged_adversary \<Rightarrow> prob"
  where
    "ro_absorb_checked_staged_adversary_acceptance_probability A =
      wp_event (ro_absorb_checked_staged_security_experiment A)
        (\<lambda>out. \<not> Option.is_none out) adversary_initial_state"

definition ro_checked_staged_security_hash_query_budget_for ::
  "staged_budgets \<Rightarrow> nat" where
  "ro_checked_staged_security_hash_query_budget_for budgets =
    ro_checked_staged_transcript_hash_query_budget_for budgets +
    verifier_hash_query_budget"

lemma hash_target_program_verifier_state_transfer:
  "hash_target_program B 0 (verifier_state_transfer tr)"
  by (rule hash_map_preserving_imp_hash_target_program_zero)
    (rule hash_map_preserving_verifier_state_transfer)

lemma hash_target_program_verifier_after_adversary:
  "hash_target_program B verifier_hash_query_budget
    (verifier_state_transfer tr \<bind> (\<lambda>_. verify_monad))"
proof -
  have target:
    "hash_target_program B (0 + verifier_hash_query_budget)
      (verifier_state_transfer tr \<bind> (\<lambda>_. verify_monad))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_verifier_state_transfer,
        rule hash_target_program_verify_monad)
  then show ?thesis by simp
qed

definition ro_checked_verifier_state_transfer_with_saved
  :: "'f list \<Rightarrow> ('f protocol_channel, 'f protocol_channel) state_monad"
  where
    "ro_checked_verifier_state_transfer_with_saved tr =
      get \<bind> (\<lambda>s.
        put (verifier_state_from_adversary s tr) \<bind>
        (\<lambda>_. return s))"

lemma hash_map_preserving_ro_checked_verifier_state_transfer_with_saved:
  "hash_map_preserving
    (ro_checked_verifier_state_transfer_with_saved tr)"
  unfolding hash_map_preserving_def
    ro_checked_verifier_state_transfer_with_saved_def
  by (auto elim!: set_dist_bindE)

lemma hash_range_budget_ro_checked_verifier_state_transfer_with_saved:
  "hash_range_budget 0
    (ro_checked_verifier_state_transfer_with_saved tr)"
  by (rule hash_map_preserving_imp_hash_range_budget_zero_semantic)
    (rule hash_map_preserving_ro_checked_verifier_state_transfer_with_saved)

lemma hash_collision_budget_ro_checked_verifier_state_transfer_with_saved:
  "hash_collision_budget 0
    (ro_checked_verifier_state_transfer_with_saved tr)"
  by (rule hash_map_preserving_imp_hash_collision_budget_zero_semantic)
    (rule hash_map_preserving_ro_checked_verifier_state_transfer_with_saved)

lemma hash_target_program_ro_checked_verifier_state_transfer_with_saved:
  "hash_target_program B 0
    (ro_checked_verifier_state_transfer_with_saved tr)"
  by (rule hash_map_preserving_imp_hash_target_program_zero)
    (rule hash_map_preserving_ro_checked_verifier_state_transfer_with_saved)

lemma hash_range_budget_ro_checked_staged_security_experiment:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (ro_checked_staged_security_hash_query_budget_for budgets)
      (ro_checked_staged_security_experiment A)"
proof -
  have cont:
    "\<And>data. hash_range_budget verifier_hash_query_budget
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad)))"
    using hash_range_budget_verifier_after_adversary
      [of "staged_proof_transcript data" for data]
    unfolding verifier_state_transfer_def sm_bind_assoc .
  have budget:
    "hash_range_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets +
        verifier_hash_query_budget)
      (ro_checked_staged_security_experiment A)"
    unfolding ro_checked_staged_security_experiment_def
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_checked_staged_transcript_program
        [OF wf controlled], rule cont)
  then show ?thesis
    unfolding ro_checked_staged_security_hash_query_budget_for_def .
qed

lemma hash_collision_budget_ro_checked_staged_security_experiment:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_collision_budget
      (ro_checked_staged_security_hash_query_budget_for budgets)
      (ro_checked_staged_security_experiment A)"
proof -
  have cont_range:
    "\<And>data. hash_range_budget verifier_hash_query_budget
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad)))"
    using hash_range_budget_verifier_after_adversary
      [of "staged_proof_transcript data" for data]
    unfolding verifier_state_transfer_def sm_bind_assoc .
  have cont_collision:
    "\<And>data. hash_collision_budget verifier_hash_query_budget
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad)))"
    using hash_collision_budget_verifier_after_adversary
      [of "staged_proof_transcript data" for data]
    unfolding verifier_state_transfer_def sm_bind_assoc .
  have budget:
    "hash_collision_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets +
        verifier_hash_query_budget)
      (ro_checked_staged_security_experiment A)"
    unfolding ro_checked_staged_security_experiment_def
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_ro_checked_staged_transcript_program
        [OF wf controlled],
       rule hash_collision_budget_ro_checked_staged_transcript_program
        [OF wf controlled],
       rule cont_range, rule cont_collision)
  then show ?thesis
    unfolding ro_checked_staged_security_hash_query_budget_for_def .
qed

lemma hash_target_program_ro_checked_staged_security_experiment:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (ro_checked_staged_security_hash_query_budget_for budgets)
      (ro_checked_staged_security_experiment A)"
proof -
  have cont:
    "\<And>data. hash_target_program B verifier_hash_query_budget
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad)))"
    using hash_target_program_verifier_after_adversary
      [of B "staged_proof_transcript data" for data]
    unfolding verifier_state_transfer_def sm_bind_assoc .
  have budget:
    "hash_target_program B
      (ro_checked_staged_transcript_hash_query_budget_for budgets +
        verifier_hash_query_budget)
      (ro_checked_staged_security_experiment A)"
    unfolding ro_checked_staged_security_experiment_def
    by (rule hash_target_program_bind)
      (rule hash_target_program_ro_checked_staged_transcript_program
        [OF wf controlled], rule cont)
  then show ?thesis
    unfolding ro_checked_staged_security_hash_query_budget_for_def .
qed

lemma hash_range_budget_ro_checked_staged_security_experiment_with_data_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (ro_checked_staged_security_hash_query_budget_for budgets)
      (ro_checked_staged_security_experiment_with_data_state A)"
proof -
  let ?head = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have verify_return_range:
    "\<And>data saved. hash_range_budget (verifier_hash_query_budget + 0)
      (verify_monad \<bind>
        (\<lambda>result. return ((data, saved), result)))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_verify_monad, rule hash_range_budget_return)
  have cont_range:
    "\<And>data. hash_range_budget (0 + (verifier_hash_query_budget + 0))
      (ro_checked_verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>saved. verify_monad \<bind>
          (\<lambda>result. return ((data, saved), result))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_checked_verifier_state_transfer_with_saved,
        rule verify_return_range)
  have whole:
    "hash_range_budget
      (?head + (0 + (verifier_hash_query_budget + 0)))
      (ro_checked_staged_transcript_program A \<bind>
        (\<lambda>data.
          ro_checked_verifier_state_transfer_with_saved
            (staged_proof_transcript data) \<bind>
          (\<lambda>saved. verify_monad \<bind>
            (\<lambda>result. return ((data, saved), result)))))"
    by (rule hash_range_budget_bind)
      (rule
        hash_range_budget_ro_checked_staged_transcript_program[OF wf controlled],
        rule cont_range)
  show ?thesis
    using whole
    unfolding ro_checked_staged_security_experiment_with_data_state_def
      ro_checked_verifier_state_transfer_with_saved_def
      ro_checked_staged_security_hash_query_budget_for_def
    by (simp add: sm_bind_assoc add.assoc)
qed

lemma hash_collision_budget_ro_checked_staged_security_experiment_with_data_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_collision_budget
      (ro_checked_staged_security_hash_query_budget_for budgets)
      (ro_checked_staged_security_experiment_with_data_state A)"
proof -
  let ?head = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have verify_return_range:
    "\<And>data saved. hash_range_budget (verifier_hash_query_budget + 0)
      (verify_monad \<bind>
        (\<lambda>result. return ((data, saved), result)))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_verify_monad, rule hash_range_budget_return)
  have verify_return_collision:
    "\<And>data saved. hash_collision_budget (verifier_hash_query_budget + 0)
      (verify_monad \<bind>
        (\<lambda>result. return ((data, saved), result)))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_verify_monad,
       rule hash_collision_budget_verify_monad,
       rule hash_range_budget_return, rule hash_collision_budget_return)
  have cont_range:
    "\<And>data. hash_range_budget (0 + (verifier_hash_query_budget + 0))
      (ro_checked_verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>saved. verify_monad \<bind>
          (\<lambda>result. return ((data, saved), result))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_ro_checked_verifier_state_transfer_with_saved,
        rule verify_return_range)
  have cont_collision:
    "\<And>data. hash_collision_budget (0 + (verifier_hash_query_budget + 0))
      (ro_checked_verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>saved. verify_monad \<bind>
          (\<lambda>result. return ((data, saved), result))))"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_ro_checked_verifier_state_transfer_with_saved,
       rule hash_collision_budget_ro_checked_verifier_state_transfer_with_saved,
       rule verify_return_range, rule verify_return_collision)
  have whole:
    "hash_collision_budget
      (?head + (0 + (verifier_hash_query_budget + 0)))
      (ro_checked_staged_transcript_program A \<bind>
        (\<lambda>data.
          ro_checked_verifier_state_transfer_with_saved
            (staged_proof_transcript data) \<bind>
          (\<lambda>saved. verify_monad \<bind>
            (\<lambda>result. return ((data, saved), result)))))"
    by (rule hash_collision_budget_bind)
      (rule
        hash_range_budget_ro_checked_staged_transcript_program[OF wf controlled],
       rule
        hash_collision_budget_ro_checked_staged_transcript_program[OF wf controlled],
       rule cont_range, rule cont_collision)
  show ?thesis
    using whole
    unfolding ro_checked_staged_security_experiment_with_data_state_def
      ro_checked_verifier_state_transfer_with_saved_def
      ro_checked_staged_security_hash_query_budget_for_def
    by (simp add: sm_bind_assoc add.assoc)
qed

lemma hash_target_program_ro_checked_staged_security_experiment_with_data_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_target_program B
      (ro_checked_staged_security_hash_query_budget_for budgets)
      (ro_checked_staged_security_experiment_with_data_state A)"
proof -
  let ?head = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have verify_return_target:
    "\<And>data saved. hash_target_program B (verifier_hash_query_budget + 0)
      (verify_monad \<bind>
        (\<lambda>result. return ((data, saved), result)))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_verify_monad, rule hash_target_program_return)
  have cont_target:
    "\<And>data. hash_target_program B (0 + (verifier_hash_query_budget + 0))
      (ro_checked_verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>saved. verify_monad \<bind>
          (\<lambda>result. return ((data, saved), result))))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_ro_checked_verifier_state_transfer_with_saved,
        rule verify_return_target)
  have whole:
    "hash_target_program B
      (?head + (0 + (verifier_hash_query_budget + 0)))
      (ro_checked_staged_transcript_program A \<bind>
        (\<lambda>data.
          ro_checked_verifier_state_transfer_with_saved
            (staged_proof_transcript data) \<bind>
          (\<lambda>saved. verify_monad \<bind>
            (\<lambda>result. return ((data, saved), result)))))"
    by (rule hash_target_program_bind)
      (rule
        hash_target_program_ro_checked_staged_transcript_program[OF wf controlled],
        rule cont_target)
  show ?thesis
    using whole
    unfolding ro_checked_staged_security_experiment_with_data_state_def
      ro_checked_verifier_state_transfer_with_saved_def
      ro_checked_staged_security_hash_query_budget_for_def
    by (simp add: sm_bind_assoc add.assoc)
qed

lemma ro_checked_staged_security_experiment_hash_new_collision_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (ro_checked_staged_security_experiment A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (ro_checked_staged_security_hash_query_budget_for budgets)"
proof -
  let ?q = "ro_checked_staged_security_hash_query_budget_for budgets"
  have collision_budget:
    "hash_collision_budget ?q (ro_checked_staged_security_experiment A)"
    by (rule hash_collision_budget_ro_checked_staged_security_experiment
        [OF wf controlled])
  have "wp_event (ro_checked_staged_security_experiment A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value
        (card (hash_map_output_values adversary_initial_state)) ?q"
    using collision_budget adversary_initial_state_no_output_collision
    unfolding hash_collision_budget_def by blast
  then show ?thesis by simp
qed

lemma ro_checked_staged_security_experiment_hash_map_output_collision_bad_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (ro_checked_staged_security_experiment A)
      (hash_map_output_collision_bad adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (ro_checked_staged_security_hash_query_budget_for budgets)"
proof -
  have "wp_event (ro_checked_staged_security_experiment A)
      (hash_map_output_collision_bad adversary_initial_state)
      adversary_initial_state \<le>
      wp_event (ro_checked_staged_security_experiment A)
        (hash_new_collision_event adversary_initial_state)
        adversary_initial_state"
    by (rule wp_event_mono)
      (rule hash_map_output_collision_bad_imp_security_new_collision)
  also have "... \<le>
      hash_collision_budget_value 0
        (ro_checked_staged_security_hash_query_budget_for budgets)"
    by (rule ro_checked_staged_security_experiment_hash_new_collision_bound_controlled
        [OF wf controlled])
  finally show ?thesis .
qed

text \<open>
  This layer intentionally stops at security-level range/collision/target
  accounting.  The transcript builder already has a relation-budget wrapper,
  but the verifier side has no corresponding relation-budget theorem yet.
\<close>

end

end
