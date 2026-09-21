theory Soundness_FRI_Robust_Balanced_Schedule
  imports Stark.Soundness_FRI_Robust_Exact_Rate_Multiround
begin

context soundness
begin

definition fri_balanced_margin :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fri_balanced_margin C i =
    (length (fri_canonical_domain_at (Suc i)) + C - 1) div C"

definition fri_balanced_radius :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fri_balanced_radius m C i =
    (\<Sum>j=i..<m. 2 ^ (j - i + 1) * fri_balanced_margin C j)"

definition fri_balanced_good_radius :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fri_balanced_good_radius m C i =
    fri_balanced_radius m C (Suc i) + fri_balanced_margin C i"

lemma fri_balanced_radius_terminal[simp]:
  "fri_balanced_radius m C m = 0"
  unfolding fri_balanced_radius_def by simp

lemma fri_balanced_radius_step:
  assumes "i < m"
  shows "fri_balanced_radius m C i =
    2 * fri_balanced_good_radius m C i"
proof -
  have interval:
      "{i..<m} = insert i {Suc i..<m}"
    using assms by auto
  have i_not: "i \<notin> {Suc i..<m}"
    by simp
  have exponent:
      "\<And>j. j \<in> {Suc i..<m} \<Longrightarrow>
        2 ^ (j - i + 1) = 2 * 2 ^ (j - Suc i + 1)"
  proof -
    fix j
    assume j_in: "j \<in> {Suc i..<m}"
    then obtain k where j_eq: "j = Suc i + k"
      by (metis atLeastLessThan_iff le_iff_add)
    show "2 ^ (j - i + 1) = 2 * 2 ^ (j - Suc i + 1)"
      unfolding j_eq by simp
  qed
  have
      "fri_balanced_radius m C i =
        2 * fri_balanced_margin C i +
          (\<Sum>j=Suc i..<m.
            2 ^ (j - i + 1) * fri_balanced_margin C j)"
    unfolding fri_balanced_radius_def interval
    by (simp add: i_not)
  also have "... =
      2 * fri_balanced_margin C i +
        2 * (\<Sum>j=Suc i..<m.
          2 ^ (j - Suc i + 1) * fri_balanced_margin C j)"
  proof -
    have rest:
        "(\<Sum>j=Suc i..<m.
            2 ^ (j - i + 1) * fri_balanced_margin C j) =
          2 * (\<Sum>j=Suc i..<m.
            2 ^ (j - Suc i + 1) * fri_balanced_margin C j)"
    proof -
      have
          "(\<Sum>j=Suc i..<m.
              2 ^ (j - i + 1) * fri_balanced_margin C j) =
            (\<Sum>j=Suc i..<m.
              2 * (2 ^ (j - Suc i + 1) *
                fri_balanced_margin C j))"
      proof (rule sum.cong)
        show "{Suc i..<m} = {Suc i..<m}" by simp
        fix j
        assume j_in: "j \<in> {Suc i..<m}"
        have e:
            "2 ^ (j - i + 1) =
              2 * 2 ^ (j - Suc i + 1)"
          by (rule exponent[OF j_in])
        show
            "2 ^ (j - i + 1) * fri_balanced_margin C j =
              2 * (2 ^ (j - Suc i + 1) *
                fri_balanced_margin C j)"
          unfolding e by (simp add: algebra_simps)
      qed
      also have "... =
          2 * (\<Sum>j=Suc i..<m.
            2 ^ (j - Suc i + 1) * fri_balanced_margin C j)"
        by (simp only: sum_distrib_left)
      finally show ?thesis .
    qed
    show ?thesis using rest by simp
  qed
  also have "... = 2 * fri_balanced_good_radius m C i"
    unfolding fri_balanced_good_radius_def fri_balanced_radius_def
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma fri_balanced_current_radius_exact:
  assumes "i < m"
  shows "2 * fri_balanced_good_radius m C i =
    fri_balanced_radius m C i"
  using fri_balanced_radius_step[OF assms] by simp

lemma fri_balanced_transition_margin_exact:
  "fri_balanced_radius m C (Suc i) + fri_balanced_margin C i =
    fri_balanced_good_radius m C i"
  unfolding fri_balanced_good_radius_def by simp

lemma fri_balanced_radius_initial_mono:
  assumes "m \<le> M"
  shows "fri_balanced_radius m C 0 \<le> fri_balanced_radius M C 0"
  unfolding fri_balanced_radius_def
  by (rule sum_mono2) (use assms in auto)

definition fri_balanced_exact_list_cap_at ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "fri_balanced_exact_list_cap_at d m C L i \<longleftrightarrow>
    (let n = length (fri_canonical_domain_at i);
         degree = fri_degree_after i (fri_padded_degree_bound d);
         radius = 4 * fri_balanced_good_radius m C i
     in radius \<le> n \<and>
        degree \<le> n \<and>
        n * degree < (n - radius)^2 \<and>
        n * (n - degree) div ((n - radius)^2 - n * degree) \<le> L)"

definition fri_balanced_exact_list_cap ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "fri_balanced_exact_list_cap d m C L \<longleftrightarrow>
    (\<forall>i<m. fri_balanced_exact_list_cap_at d m C L i)"

lemma fri_balanced_exact_list_capD:
  assumes exact: "fri_balanced_exact_list_cap d m C L"
    and active: "i < m"
  obtains
    "4 * fri_balanced_good_radius m C i \<le>
      length (fri_canonical_domain_at i)"
    "fri_degree_after i (fri_padded_degree_bound d) \<le>
      length (fri_canonical_domain_at i)"
    "length (fri_canonical_domain_at i) *
        fri_degree_after i (fri_padded_degree_bound d) <
      (length (fri_canonical_domain_at i) -
        4 * fri_balanced_good_radius m C i)^2"
    "length (fri_canonical_domain_at i) *
        (length (fri_canonical_domain_at i) -
          fri_degree_after i (fri_padded_degree_bound d)) div
        ((length (fri_canonical_domain_at i) -
            4 * fri_balanced_good_radius m C i)^2 -
          length (fri_canonical_domain_at i) *
            fri_degree_after i (fri_padded_degree_bound d)) \<le> L"
  using exact active
  unfolding fri_balanced_exact_list_cap_def
    fri_balanced_exact_list_cap_at_def Let_def
  by blast

lemma fri_rs_active_layer_balanced_exact_list_cap:
  assumes eval_power: "clength * scale = 2 ^ N"
    and active: "i < m"
    and rounds_fit: "m \<le> N"
    and exact: "fri_balanced_exact_list_cap d m C L"
  shows
    "card (fri_rs_close_list
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        received
        (4 * fri_balanced_good_radius m C i)) \<le> L"
proof -
  have i_le: "i \<le> N"
    using active rounds_fit by linarith
  have distinct_domain: "distinct (fri_canonical_domain_at i)"
    by (rule distinct_fri_canonical_domain_at[OF eval_power i_le])
  have radius:
      "4 * fri_balanced_good_radius m C i \<le>
        length (fri_canonical_domain_at i)"
    and degree:
      "fri_degree_after i (fri_padded_degree_bound d) \<le>
        length (fri_canonical_domain_at i)"
    and johnson:
      "length (fri_canonical_domain_at i) *
          fri_degree_after i (fri_padded_degree_bound d) <
        (length (fri_canonical_domain_at i) -
          4 * fri_balanced_good_radius m C i)^2"
    and envelope:
      "length (fri_canonical_domain_at i) *
          (length (fri_canonical_domain_at i) -
            fri_degree_after i (fri_padded_degree_bound d)) div
          ((length (fri_canonical_domain_at i) -
              4 * fri_balanced_good_radius m C i)^2 -
            length (fri_canonical_domain_at i) *
              fri_degree_after i (fri_padded_degree_bound d)) \<le> L"
    using exact active
    unfolding fri_balanced_exact_list_cap_def
      fri_balanced_exact_list_cap_at_def Let_def
    by blast+
  have bound:
      "card (fri_rs_close_list
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i)
          received
          (4 * fri_balanced_good_radius m C i)) \<le>
        length (fri_canonical_domain_at i) *
          (length (fri_canonical_domain_at i) -
            fri_degree_after i (fri_padded_degree_bound d)) div
          ((length (fri_canonical_domain_at i) -
              4 * fri_balanced_good_radius m C i)^2 -
            length (fri_canonical_domain_at i) *
              fri_degree_after i (fri_padded_degree_bound d))"
    by (rule fri_rs_close_list_card_div_bound[
          OF distinct_domain radius degree johnson])
  show ?thesis
    using bound envelope by linarith
qed

lemma fri_canonical_multiround_balanced_decode_or_reject_exact_two:
  fixes d N m C :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and rounds_fit: "Suc m \<le> N"
    and exact: "fri_balanced_exact_list_cap d m C 2"
    and layer_length:
      "\<And>i. i \<le> m \<Longrightarrow>
        length (layers ! i) = length (fri_canonical_domain_at i)"
    and terminal_close:
      "fri_canonical_layer_close d layers
        (fri_balanced_radius m C) m"
  shows
    "fri_canonical_layer_close d layers
        (fri_balanced_radius m C) 0 \<or>
      (\<exists>i<m.
        \<not> fri_canonical_layer_close d layers
            (fri_balanced_radius m C) i \<and>
        fri_canonical_layer_close d layers
            (fri_balanced_radius m C) (Suc i) \<and>
        ((bs ! i \<in>
            fri_canonical_layer_good_challenges
              d layers (fri_balanced_good_radius m C) i \<and>
          card (fri_canonical_layer_good_challenges
              d layers (fri_balanced_good_radius m C) i) \<le>
            2 * fri_balanced_good_radius m C i + 3) \<or>
         card (fri_canonical_transition_agreement_indices
              bs layers i) \<le>
            length (fri_canonical_domain_at (Suc i)) -
              fri_balanced_margin C i))"
proof (rule fri_canonical_multiround_decode_or_reject_at_list_cap_two[
    where N=N and m=m
      and radius="fri_balanced_radius m C"
      and good_radius="fri_balanced_good_radius m C"
      and margin="fri_balanced_margin C"])
  show "clength * scale = 2 ^ N" by (rule eval_power)
  show "m = ceil_log (Suc d)" by (rule rounds_eq)
  show "Suc m \<le> N" by (rule rounds_fit)
  fix i
  assume "i \<le> m"
  show "length (layers ! i) =
      length (fri_canonical_domain_at i)"
    by (rule layer_length[OF \<open>i \<le> m\<close>])
next
  show "fri_canonical_layer_close d layers
      (fri_balanced_radius m C) m"
    by (rule terminal_close)
next
  fix i
  assume i_bound: "i < m"
  show "2 * fri_balanced_good_radius m C i \<le>
      fri_balanced_radius m C i"
    using fri_balanced_current_radius_exact[OF i_bound] by simp
next
  fix i
  assume "i < m"
  show "fri_balanced_radius m C (Suc i) +
      fri_balanced_margin C i \<le>
      fri_balanced_good_radius m C i"
    unfolding fri_balanced_transition_margin_exact by simp
next
  fix i
  assume i_bound: "i < m"
  show
    "card (fri_rs_close_list
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i) (nth (layers ! i))
        (4 * fri_balanced_good_radius m C i)) \<le> 2"
    by (rule fri_rs_active_layer_balanced_exact_list_cap[
          OF eval_power i_bound _ exact])
      (use rounds_fit in linarith)
qed

end
end
