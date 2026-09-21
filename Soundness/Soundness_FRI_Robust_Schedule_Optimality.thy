theory Soundness_FRI_Robust_Schedule_Optimality
  imports Stark.Soundness_FRI_Robust_Balanced_Selected_Residual
begin

context soundness
begin

text \<open>
  This theory audits the arbitrary radius/good-radius/margin interface already
  accepted by the robust multiround theorem.  The scale-64 numeral lemmas are a
  diagnostic optimization certificate for that proof interface; they are not
  a concrete cryptographic profile or a lower bound for FRI protocols.
\<close>

fun fri_schedule_margin_cost :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "fri_schedule_margin_cost 0 margin i = 0"
| "fri_schedule_margin_cost (Suc n) margin i =
    margin i + 2 * fri_schedule_margin_cost n margin (Suc i)"

lemma fri_schedule_margin_cost_le_good:
  assumes current_radius:
      "\<And>j. i \<le> j \<Longrightarrow> j < i + n \<Longrightarrow> 2 * good j \<le> radius j"
    and transition_margin:
      "\<And>j. i \<le> j \<Longrightarrow> j < i + n \<Longrightarrow>
        radius (Suc j) + margin j \<le> good j"
  shows "fri_schedule_margin_cost n margin i \<le> good i"
  using current_radius transition_margin
proof (induction n arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have transition:
      "radius (Suc i) + margin i \<le> good i"
    by (rule Suc.prems(2)) simp_all
  show ?case
  proof (cases n)
    case 0
    then show ?thesis
      using transition by simp
  next
    case (Suc k)
    have tail:
        "fri_schedule_margin_cost n margin (Suc i) \<le> good (Suc i)"
    proof (rule Suc.IH)
      fix j
      assume lo: "Suc i \<le> j"
        and hi: "j < Suc i + n"
      show "2 * good j \<le> radius j"
        by (rule Suc.prems(1))
          (use lo hi in simp_all)
    next
      fix j
      assume lo: "Suc i \<le> j"
        and hi: "j < Suc i + n"
      show "radius (Suc j) + margin j \<le> good j"
        by (rule Suc.prems(2))
          (use lo hi in simp_all)
    qed
    have current:
        "2 * good (Suc i) \<le> radius (Suc i)"
      by (rule Suc.prems(1))
        (use Suc in simp_all)
    show ?thesis
      using tail current transition by simp
  qed
qed
definition fri_schedule_exact_list_cap_at ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "fri_schedule_exact_list_cap_at d good L i \<longleftrightarrow>
    (let n = length (fri_canonical_domain_at i);
         degree = fri_degree_after i (fri_padded_degree_bound d);
         reconstruction_radius = 4 * good i
     in reconstruction_radius \<le> n \<and>
        degree \<le> n \<and>
        n * degree < (n - reconstruction_radius)^2 \<and>
        n * (n - degree) div
          ((n - reconstruction_radius)^2 - n * degree) \<le> L)"

definition fri_schedule_good_radius ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "fri_schedule_good_radius m margin i =
    fri_schedule_margin_cost (m - i) margin i"

definition fri_schedule_radius ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "fri_schedule_radius m margin i =
    2 * fri_schedule_good_radius m margin i"

lemma fri_schedule_radius_terminal[simp]:
  "fri_schedule_radius m margin m = 0"
  unfolding fri_schedule_radius_def fri_schedule_good_radius_def by simp

lemma fri_schedule_current_radius_exact:
  "2 * fri_schedule_good_radius m margin i =
    fri_schedule_radius m margin i"
  unfolding fri_schedule_radius_def by simp

lemma fri_schedule_transition_margin_exact:
  assumes "i < m"
  shows "fri_schedule_radius m margin (Suc i) + margin i =
    fri_schedule_good_radius m margin i"
proof -
  have diff: "m - i = Suc (m - Suc i)"
    using assms using assms by simp
  show ?thesis
    unfolding fri_schedule_radius_def fri_schedule_good_radius_def
    by (simp add: diff)
qed

definition fri_schedule_exact_list_cap ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
where
  "fri_schedule_exact_list_cap d m margin L \<longleftrightarrow>
    (\<forall>i<m. fri_schedule_exact_list_cap_at d
      (fri_schedule_good_radius m margin) L i)"

lemma fri_rs_active_layer_schedule_exact_list_cap:
  assumes eval_power: "clength * scale = 2 ^ N"
    and active: "i < m"
    and rounds_fit: "m \<le> N"
    and exact: "fri_schedule_exact_list_cap d m margin L"
  shows
    "card (fri_rs_close_list
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i) received
        (4 * fri_schedule_good_radius m margin i)) \<le> L"
proof -
  have i_le: "i \<le> N"
    using active rounds_fit by linarith
  have distinct_domain: "distinct (fri_canonical_domain_at i)"
    by (rule distinct_fri_canonical_domain_at[OF eval_power i_le])
  have radius:
      "4 * fri_schedule_good_radius m margin i \<le>
        length (fri_canonical_domain_at i)"
    and degree:
      "fri_degree_after i (fri_padded_degree_bound d) \<le>
        length (fri_canonical_domain_at i)"
    and johnson:
      "length (fri_canonical_domain_at i) *
          fri_degree_after i (fri_padded_degree_bound d) <
        (length (fri_canonical_domain_at i) -
          4 * fri_schedule_good_radius m margin i)^2"
    and envelope:
      "length (fri_canonical_domain_at i) *
          (length (fri_canonical_domain_at i) -
            fri_degree_after i (fri_padded_degree_bound d)) div
          ((length (fri_canonical_domain_at i) -
              4 * fri_schedule_good_radius m margin i)^2 -
            length (fri_canonical_domain_at i) *
              fri_degree_after i (fri_padded_degree_bound d)) \<le> L"
    using exact active
    unfolding fri_schedule_exact_list_cap_def
      fri_schedule_exact_list_cap_at_def Let_def
    by blast+
  have bound:
      "card (fri_rs_close_list
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i) received
          (4 * fri_schedule_good_radius m margin i)) \<le>
        length (fri_canonical_domain_at i) *
          (length (fri_canonical_domain_at i) -
            fri_degree_after i (fri_padded_degree_bound d)) div
          ((length (fri_canonical_domain_at i) -
              4 * fri_schedule_good_radius m margin i)^2 -
            length (fri_canonical_domain_at i) *
              fri_degree_after i (fri_padded_degree_bound d))"
    by (rule fri_rs_close_list_card_div_bound[
          OF distinct_domain radius degree johnson])
  show ?thesis
    using bound envelope by linarith
qed

lemma fri_canonical_multiround_schedule_decode_or_reject_exact_two:
  fixes d N m :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and rounds_eq: "m = ceil_log (Suc d)"
    and rounds_fit: "Suc m \<le> N"
    and exact: "fri_schedule_exact_list_cap d m margin 2"
    and layer_length:
      "\<And>i. i \<le> m \<Longrightarrow>
        length (layers ! i) = length (fri_canonical_domain_at i)"
    and terminal_close:
      "fri_canonical_layer_close d layers
        (fri_schedule_radius m margin) m"
  shows
    "fri_canonical_layer_close d layers
        (fri_schedule_radius m margin) 0 \<or>
      (\<exists>i<m.
        \<not> fri_canonical_layer_close d layers
            (fri_schedule_radius m margin) i \<and>
        fri_canonical_layer_close d layers
            (fri_schedule_radius m margin) (Suc i) \<and>
        ((bs ! i \<in>
            fri_canonical_layer_good_challenges
              d layers (fri_schedule_good_radius m margin) i \<and>
          card (fri_canonical_layer_good_challenges
              d layers (fri_schedule_good_radius m margin) i) \<le>
            2 * fri_schedule_good_radius m margin i + 3) \<or>
         card (fri_canonical_transition_agreement_indices
              bs layers i) \<le>
            length (fri_canonical_domain_at (Suc i)) - margin i))"
proof (rule fri_canonical_multiround_decode_or_reject_at_list_cap_two[
    where N=N and m=m
      and radius="fri_schedule_radius m margin"
      and good_radius="fri_schedule_good_radius m margin"
      and margin=margin])
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
      (fri_schedule_radius m margin) m"
    by (rule terminal_close)
next
  fix i
  assume "i < m"
  show "2 * fri_schedule_good_radius m margin i \<le>
      fri_schedule_radius m margin i"
    unfolding fri_schedule_current_radius_exact by simp
next
  fix i
  assume i_bound: "i < m"
  show "fri_schedule_radius m margin (Suc i) + margin i \<le>
      fri_schedule_good_radius m margin i"
    using fri_schedule_transition_margin_exact[OF i_bound] by simp
next
  fix i
  assume i_bound: "i < m"
  show
    "card (fri_rs_close_list
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i) (nth (layers ! i))
        (4 * fri_schedule_good_radius m margin i)) \<le> 2"
    by (rule fri_rs_active_layer_schedule_exact_list_cap[
          OF eval_power i_bound _ exact])
      (use rounds_fit in linarith)
qed

lemma fri_schedule_margin_cost_mono:
  assumes margins:
    "\<And>j. i \<le> j \<Longrightarrow> j < i + n \<Longrightarrow> small j \<le> large j"
  shows "fri_schedule_margin_cost n small i \<le>
    fri_schedule_margin_cost n large i"
  using margins
proof (induction n arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have head: "small i \<le> large i"
    by (rule Suc.prems) simp_all
  have tail:
      "fri_schedule_margin_cost n small (Suc i) \<le>
        fri_schedule_margin_cost n large (Suc i)"
  proof (rule Suc.IH)
    fix j
    assume lo: "Suc i \<le> j"
      and hi: "j < Suc i + n"
    show "small j \<le> large j"
      by (rule Suc.prems)
        (use lo hi in simp_all)
  qed
  show ?case
    using head tail by simp
qed

definition fri_list_cap_arithmetic ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "fri_list_cap_arithmetic n_nat d_nat good_nat cap_nat \<longleftrightarrow>
    4 * good_nat \<le> n_nat \<and>
    d_nat \<le> n_nat \<and>
    n_nat * d_nat < (n_nat - 4 * good_nat)^2 \<and>
    n_nat * (n_nat - d_nat) div
      ((n_nat - 4 * good_nat)^2 - n_nat * d_nat) \<le> cap_nat"

lemma fri_scale64_first_layer_good_capacity:
  assumes cap: "fri_list_cap_arithmetic 65536 1023 good 2"
  shows "good \<le> 6778"
  proof (rule ccontr)
  assume not_le: "\<not> good \<le> 6778"
  have radius_le: "4 * good \<le> 65536"
    and johnson:
      "65536 * 1023 < (65536 - 4 * good)^2"
    and quotient:
      "65536 * (65536 - 1023) div
        ((65536 - 4 * good)^2 - 65536 * 1023) \<le> 2"
    using cap unfolding fri_list_cap_arithmetic_def by blast+
  have denominator_pos:
      "0 < (65536 - 4 * good)^2 - 65536 * 1023"
    using johnson by linarith
  have quotient_lt:
      "65536 * (65536 - 1023) div
        ((65536 - 4 * good)^2 - 65536 * 1023) < 3"
    using quotient by linarith
  have numerator_lt:
      "65536 * (65536 - 1023) <
        3 * ((65536 - 4 * good)^2 - 65536 * 1023)"
    using quotient_lt
      div_less_iff_less_mult[OF denominator_pos] by blast
  have good_lower: "6779 \<le> good"
    using not_le by linarith
  have remainder_le: "65536 - 4 * good \<le> 38420"
    using good_lower radius_le by linarith
  have square_le:
      "(65536 - 4 * good)^2 \<le> 38420^2"
    unfolding power2_eq_square
    by (intro mult_le_mono remainder_le)
  have denominator_le:
      "(65536 - 4 * good)^2 - 65536 * 1023 \<le>
        38420^2 - 65536 * 1023"
    by (rule Nat.diff_le_mono[OF square_le])
  have upper:
      "3 * ((65536 - 4 * good)^2 - 65536 * 1023) \<le>
        65536 * (65536 - 1023)"
    using denominator_le by simp
  show False
    using numerator_lt upper by linarith
qed
lemma fri_schedule_scale64_first_layer_good_capacity:
  assumes eval_size: "clength * scale = 65536"
    and cap: "fri_schedule_exact_list_cap_at 1023 good 2 0"
  shows "good 0 \<le> 6778"
proof -
  have log: "ceil_log 1024 = 10"
    unfolding ceil_log_def by eval
  have arithmetic:
      "fri_list_cap_arithmetic 65536 1023 (good 0) 2"
    using cap eval_size
    unfolding fri_schedule_exact_list_cap_at_def
      fri_list_cap_arithmetic_def fri_canonical_domain_at_length
      fri_degree_after_closed_form fri_padded_degree_bound_def Let_def
    by (simp add: log)
  show ?thesis
    by (rule fri_scale64_first_layer_good_capacity[OF arithmetic])
qed
lemma modulo_envelope_le_imp_margin:
  assumes radius_pos: "0 < required_nat"
    and boundary:
      "bound_nat < modulo_preimage_card_envelope N_nat q_nat
        (q_nat - (required_nat - 1))"
    and accepted:
      "modulo_preimage_card_envelope N_nat q_nat
        (q_nat - actual_nat) \<le> bound_nat"
  shows "required_nat \<le> actual_nat"
proof (rule ccontr)
  assume not_le: "\<not> required_nat \<le> actual_nat"
  have actual_le: "actual_nat \<le> required_nat - 1"
    using not_le radius_pos by linarith
  have remaining:
      "q_nat - (required_nat - 1) \<le> q_nat - actual_nat"
    by (rule Nat.diff_le_mono2[OF actual_le])
  have envelope:
      "modulo_preimage_card_envelope N_nat q_nat
          (q_nat - (required_nat - 1)) \<le>
        modulo_preimage_card_envelope N_nat q_nat
          (q_nat - actual_nat)"
    by (rule modulo_preimage_card_envelope_mono[OF remaining])
  show False
    using boundary envelope accepted by linarith
qed
definition fri_scale64_successor_size :: "nat \<Rightarrow> nat" where
  "fri_scale64_successor_size i = 32768 div 2 ^ i"

definition fri_scale64_required_margin :: "nat \<Rightarrow> nat" where
  "fri_scale64_required_margin i =
    [621, 311, 156, 78, 38, 19, 10, 5, 3, 2] ! i"

lemma fri_scale64_required_margin_boundary:
  assumes "i < 10"
  shows
    "0 < fri_scale64_required_margin i"
    "64295 < modulo_preimage_card_envelope 65472
      (fri_scale64_successor_size i)
      (fri_scale64_successor_size i -
        (fri_scale64_required_margin i - 1))"
proof -
  have cases:
      "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or>
       i = 5 \<or> i = 6 \<or> i = 7 \<or> i = 8 \<or> i = 9"
    using assms by arith
  from cases show
      "0 < fri_scale64_required_margin i"
    unfolding fri_scale64_required_margin_def by auto
  from cases show
      "64295 < modulo_preimage_card_envelope 65472
        (fri_scale64_successor_size i)
        (fri_scale64_successor_size i -
          (fri_scale64_required_margin i - 1))"
    unfolding fri_scale64_successor_size_def
      fri_scale64_required_margin_def
      modulo_preimage_card_envelope_def
    by auto
qed


lemma fri_scale64_schedule_residual_floor:
  assumes eval_size: "clength * scale = 65536"
    and first_cap:
      "fri_schedule_exact_list_cap_at 1023 good 2 0"
    and current_radius:
      "\<And>i. i < 10 \<Longrightarrow> 2 * good i \<le> radius i"
    and transition_margin:
      "\<And>i. i < 10 \<Longrightarrow> radius (Suc i) + margin i \<le> good i"
  shows
    "\<exists>i<10. 64296 \<le> modulo_preimage_card_envelope 65472
      (fri_scale64_successor_size i)
      (fri_scale64_successor_size i - margin i)"
proof (rule ccontr)
  assume no_layer:
      "\<not> (\<exists>i<10. 64296 \<le> modulo_preimage_card_envelope 65472
        (fri_scale64_successor_size i)
        (fri_scale64_successor_size i - margin i))"
  have envelope_upper:
      "\<And>i. i < 10 \<Longrightarrow> modulo_preimage_card_envelope 65472
        (fri_scale64_successor_size i)
        (fri_scale64_successor_size i - margin i) \<le> 64295"
  proof -
    fix i :: nat
    assume i_bound: "i < 10"
    have
        "\<not> 64296 \<le> modulo_preimage_card_envelope 65472
          (fri_scale64_successor_size i)
          (fri_scale64_successor_size i - margin i)"
      using no_layer i_bound by blast
    then show
        "modulo_preimage_card_envelope 65472
          (fri_scale64_successor_size i)
          (fri_scale64_successor_size i - margin i) \<le> 64295"
      by linarith
  qed
  have margin_lower:
      "\<And>i. i < 10 \<Longrightarrow> fri_scale64_required_margin i \<le> margin i"
  proof -
    fix i :: nat
    assume i_bound: "i < 10"
    have radius_pos: "0 < fri_scale64_required_margin i"
      by (rule fri_scale64_required_margin_boundary(1)[OF i_bound])
    have boundary:
        "64295 < modulo_preimage_card_envelope 65472
          (fri_scale64_successor_size i)
          (fri_scale64_successor_size i -
            (fri_scale64_required_margin i - 1))"
      by (rule fri_scale64_required_margin_boundary(2)[OF i_bound])
    show "fri_scale64_required_margin i \<le> margin i"
      by (rule modulo_envelope_le_imp_margin[
            OF radius_pos boundary envelope_upper[OF i_bound]])
  qed
  have m0: "621 \<le> margin 0"
    using margin_lower[of 0]
    unfolding fri_scale64_required_margin_def by simp
  have m1: "311 \<le> margin 1"
    using margin_lower[of 1]
    unfolding fri_scale64_required_margin_def by simp
  have m2: "156 \<le> margin 2"
    using margin_lower[of 2]
    unfolding fri_scale64_required_margin_def by simp
  have m3: "78 \<le> margin 3"
    using margin_lower[of 3]
    unfolding fri_scale64_required_margin_def by simp
  have m4: "38 \<le> margin 4"
    using margin_lower[of 4]
    unfolding fri_scale64_required_margin_def by simp
  have m5: "19 \<le> margin 5"
    using margin_lower[of 5]
    unfolding fri_scale64_required_margin_def by simp
  have m6: "10 \<le> margin 6"
    using margin_lower[of 6]
    unfolding fri_scale64_required_margin_def by simp
  have m7: "5 \<le> margin 7"
    using margin_lower[of 7]
    unfolding fri_scale64_required_margin_def by simp
  have m8: "3 \<le> margin 8"
    using margin_lower[of 8]
    unfolding fri_scale64_required_margin_def by simp
  have m9: "2 \<le> margin 9"
    using margin_lower[of 9]
    unfolding fri_scale64_required_margin_def by simp
  have g9: "2 \<le> good 9"
    using transition_margin[of 9] m9 by linarith
  have r9: "4 \<le> radius 9"
    using current_radius[of 9] g9 by linarith
  have g8: "7 \<le> good 8"
    using transition_margin[of 8, simplified] m8 r9 by linarith
  have r8: "14 \<le> radius 8"
    using current_radius[of 8] g8 by linarith
  have g7: "19 \<le> good 7"
    using transition_margin[of 7, simplified] m7 r8 by linarith
  have r7: "38 \<le> radius 7"
    using current_radius[of 7] g7 by linarith
  have g6: "48 \<le> good 6"
    using transition_margin[of 6, simplified] m6 r7 by linarith
  have r6: "96 \<le> radius 6"
    using current_radius[of 6] g6 by linarith
  have g5: "115 \<le> good 5"
    using transition_margin[of 5, simplified] m5 r6 by linarith
  have r5: "230 \<le> radius 5"
    using current_radius[of 5] g5 by linarith
  have g4: "268 \<le> good 4"
    using transition_margin[of 4, simplified] m4 r5 by linarith
  have r4: "536 \<le> radius 4"
    using current_radius[of 4] g4 by linarith
  have g3: "614 \<le> good 3"
    using transition_margin[of 3, simplified] m3 r4 by linarith
  have r3: "1228 \<le> radius 3"
    using current_radius[of 3] g3 by linarith
  have g2: "1384 \<le> good 2"
    using transition_margin[of 2, simplified] m2 r3 by linarith
  have r2: "2768 \<le> radius 2"
    using current_radius[of 2] g2 by linarith
  have raw_t1: "radius (Suc 1) + margin 1 \<le> good 1"
    using transition_margin[of 1] by simp
  have two: "Suc (1::nat) = 2"
    by eval
  have t1: "radius 2 + margin 1 \<le> good 1"
    using raw_t1 two by metis
  have g1: "3079 \<le> good 1"
    using t1 m1 r2 by linarith
  have r1: "6158 \<le> radius 1"
    using current_radius[of 1] g1 by linarith
  have t0: "radius 1 + margin 0 \<le> good 0"
    using transition_margin[of 0] by simp
  have g0: "6779 \<le> good 0"
    using t0 m0 r1 by linarith
  have cap: "good 0 \<le> 6778"
    by (rule fri_schedule_scale64_first_layer_good_capacity[
          OF eval_size first_cap])
  show False
    using g0 cap by linarith
qed

definition fri_scale64_optimal_margin :: "nat \<Rightarrow> nat" where
  "fri_scale64_optimal_margin i =
    [620, 310, 155, 78, 38, 19, 10, 5, 3, 2] ! i"

definition fri_scale64_optimal_good :: "nat \<Rightarrow> nat" where
  "fri_scale64_optimal_good i =
    [6772, 3076, 1383, 614, 268, 115, 48, 19, 7, 2] ! i"

definition fri_scale64_optimal_radius :: "nat \<Rightarrow> nat" where
  "fri_scale64_optimal_radius i =
    [13544, 6152, 2766, 1228, 536, 230, 96, 38, 14, 4, 0] ! i"

lemma fri_scale64_optimal_schedule_recurrence:
  assumes "i < 10"
  shows
    "2 * fri_scale64_optimal_good i \<le> fri_scale64_optimal_radius i"
    "fri_scale64_optimal_radius (Suc i) +
       fri_scale64_optimal_margin i \<le> fri_scale64_optimal_good i"
proof -
  have cases:
      "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or>
       i = 5 \<or> i = 6 \<or> i = 7 \<or> i = 8 \<or> i = 9"
    using assms by arith
  from cases show
      "2 * fri_scale64_optimal_good i \<le> fri_scale64_optimal_radius i"
    unfolding fri_scale64_optimal_good_def
      fri_scale64_optimal_radius_def by auto
  from cases show
      "fri_scale64_optimal_radius (Suc i) +
         fri_scale64_optimal_margin i \<le> fri_scale64_optimal_good i"
    unfolding fri_scale64_optimal_good_def
      fri_scale64_optimal_radius_def
      fri_scale64_optimal_margin_def by auto
qed

lemma fri_scale64_optimal_residual_envelope:
  assumes "i < 10"
  shows
    "modulo_preimage_card_envelope 65472
       (fri_scale64_successor_size i)
       (fri_scale64_successor_size i -
         fri_scale64_optimal_margin i) \<le> 64296"
proof -
  have cases:
      "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or>
       i = 5 \<or> i = 6 \<or> i = 7 \<or> i = 8 \<or> i = 9"
    using assms by arith
  from cases show ?thesis
    unfolding fri_scale64_successor_size_def
      fri_scale64_optimal_margin_def
      modulo_preimage_card_envelope_def
    by auto
qed

lemma fri_scale64_optimal_residual_envelope_attained:
  "modulo_preimage_card_envelope 65472
     (fri_scale64_successor_size 0)
     (fri_scale64_successor_size 0 -
       fri_scale64_optimal_margin 0) = 64296"
  unfolding fri_scale64_successor_size_def
    fri_scale64_optimal_margin_def
    modulo_preimage_card_envelope_def
  by simp

lemma fri_scale64_optimal_exact_list_cap_at:
  assumes eval_size: "clength * scale = 65536"
    and active: "i < 10"
  shows
    "fri_schedule_exact_list_cap_at 1023
      fri_scale64_optimal_good 2 i"
proof -
  have log: "ceil_log 1024 = 10"
    unfolding ceil_log_def by eval
  have cases:
      "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or>
       i = 5 \<or> i = 6 \<or> i = 7 \<or> i = 8 \<or> i = 9"
    using active by arith
  from cases eval_size show ?thesis
    unfolding fri_schedule_exact_list_cap_at_def
      fri_scale64_optimal_good_def
      fri_canonical_domain_at_length
      fri_degree_after_closed_form
      fri_padded_degree_bound_def Let_def
    by (auto simp: log)
qed

definition fri_schedule_selected_residual_index_card_bound ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
where
  "fri_schedule_selected_residual_index_card_bound d margin =
    Max (insert 0
      ((\<lambda>i. modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i)))
          (length (fri_canonical_domain_at (Suc i)) - margin i)) `
        {..<ceil_log (Suc d)}))"

lemma fri_schedule_selected_residual_index_card_bound_ge:
  assumes active: "i < ceil_log (Suc d)"
  shows
    "modulo_preimage_card_envelope query_sample_space_size
       (length (fri_canonical_domain_at (Suc i)))
       (length (fri_canonical_domain_at (Suc i)) - margin i) \<le>
     fri_schedule_selected_residual_index_card_bound d margin"
proof -
  have member:
      "modulo_preimage_card_envelope query_sample_space_size
         (length (fri_canonical_domain_at (Suc i)))
         (length (fri_canonical_domain_at (Suc i)) - margin i) \<in>
       insert 0
        ((\<lambda>j. modulo_preimage_card_envelope query_sample_space_size
            (length (fri_canonical_domain_at (Suc j)))
            (length (fri_canonical_domain_at (Suc j)) - margin j)) `
          {..<ceil_log (Suc d)})"
    using active by auto
  show ?thesis
    unfolding fri_schedule_selected_residual_index_card_bound_def
    by (rule Max_ge) (use member in auto)
qed

lemma fri_scale64_query_sample_space_size:
  assumes eval_size: "clength * scale = 65536"
    and scale_eq: "scale = 64"
    and powers_eq: "powers = 2"
  shows "query_sample_space_size = 65472"
proof -
  have max_power: "Max {0..<2::nat} = 1"
    by eval
  show ?thesis
    using eval_size scale_eq powers_eq
    unfolding query_sample_space_size_def
    by (simp add: max_power)
qed

lemma fri_scale64_successor_domain_size:
  assumes eval_size: "clength * scale = 65536"
    and active: "i < 10"
  shows
    "length (fri_canonical_domain_at (Suc i)) =
      fri_scale64_successor_size i"
proof -
  have cases:
      "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or>
       i = 5 \<or> i = 6 \<or> i = 7 \<or> i = 8 \<or> i = 9"
    using active by arith
  from cases eval_size show ?thesis
    unfolding fri_canonical_domain_at_length
      fri_scale64_successor_size_def by auto
qed

theorem fri_scale64_schedule_selected_residual_floor:
  assumes eval_size: "clength * scale = 65536"
    and scale_eq: "scale = 64"
    and powers_eq: "powers = 2"
    and first_cap:
      "fri_schedule_exact_list_cap_at 1023 good 2 0"
    and current_radius:
      "\<And>i. i < 10 \<Longrightarrow> 2 * good i \<le> radius i"
    and transition_margin:
      "\<And>i. i < 10 \<Longrightarrow> radius (Suc i) + margin i \<le> good i"
  shows
    "64296 \<le>
      fri_schedule_selected_residual_index_card_bound 1023 margin"
proof -
  have witness:
      "\<exists>i<10. 64296 \<le> modulo_preimage_card_envelope 65472
        (fri_scale64_successor_size i)
        (fri_scale64_successor_size i - margin i)"
    by (rule fri_scale64_schedule_residual_floor[
          where good=good and radius=radius and margin=margin,
          OF eval_size first_cap current_radius transition_margin])
  then obtain i where active: "i < 10"
    and lower:
      "64296 \<le> modulo_preimage_card_envelope 65472
        (fri_scale64_successor_size i)
        (fri_scale64_successor_size i - margin i)"
    by blast
  have log: "ceil_log 1024 = 10"
    unfolding ceil_log_def by eval
  have q_size: "query_sample_space_size = 65472"
    by (rule fri_scale64_query_sample_space_size[
          OF eval_size scale_eq powers_eq])
  have domain_size:
      "length (fri_canonical_domain_at (Suc i)) =
        fri_scale64_successor_size i"
    by (rule fri_scale64_successor_domain_size[OF eval_size active])
  have layer_bound:
      "modulo_preimage_card_envelope query_sample_space_size
         (length (fri_canonical_domain_at (Suc i)))
         (length (fri_canonical_domain_at (Suc i)) - margin i) \<le>
       fri_schedule_selected_residual_index_card_bound 1023 margin"
    by (rule fri_schedule_selected_residual_index_card_bound_ge)
      (use active log in simp)
  show ?thesis
    using lower layer_bound
    unfolding q_size domain_size by linarith
qed

theorem fri_scale64_optimal_selected_residual_bound:
  assumes eval_size: "clength * scale = 65536"
    and scale_eq: "scale = 64"
    and powers_eq: "powers = 2"
  shows
    "fri_schedule_selected_residual_index_card_bound 1023
       fri_scale64_optimal_margin \<le> 64296"
proof -
  have log: "ceil_log 1024 = 10"
    unfolding ceil_log_def by eval
  have q_size: "query_sample_space_size = 65472"
    by (rule fri_scale64_query_sample_space_size[
          OF eval_size scale_eq powers_eq])
  let ?bounds =
    "insert 0
      ((\<lambda>i. modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i)))
          (length (fri_canonical_domain_at (Suc i)) -
            fri_scale64_optimal_margin i)) `
        {..<ceil_log 1024})"
  have all_bounds: "\<forall>x\<in>?bounds. x \<le> 64296"
  proof (intro ballI)
    fix x
    assume member: "x \<in> ?bounds"
    show "x \<le> 64296"
    proof (cases "x = 0")
      case True
      then show ?thesis by simp
    next
      case False
      from member False obtain i where active_log:
          "i < ceil_log 1024"
        and x_eq:
          "x = modulo_preimage_card_envelope query_sample_space_size
            (length (fri_canonical_domain_at (Suc i)))
            (length (fri_canonical_domain_at (Suc i)) -
              fri_scale64_optimal_margin i)"
        by auto
      have active: "i < 10"
        using active_log log by simp
      have domain_size:
          "length (fri_canonical_domain_at (Suc i)) =
            fri_scale64_successor_size i"
        by (rule fri_scale64_successor_domain_size[OF eval_size active])
      have numeric:
          "modulo_preimage_card_envelope 65472
             (fri_scale64_successor_size i)
             (fri_scale64_successor_size i -
               fri_scale64_optimal_margin i) \<le> 64296"
        by (rule fri_scale64_optimal_residual_envelope[OF active])
      show ?thesis
        using numeric
        unfolding x_eq q_size domain_size .
    qed
  qed
  show ?thesis
    unfolding fri_schedule_selected_residual_index_card_bound_def
    apply (subst Max_le_iff)
      apply simp
     apply simp
    using all_bounds by simp
qed

end
end
