(*  Title:      Stark/Completeness_Query.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Completeness_Query
  imports Completeness_Replay
begin

text \<open>Honest query decommitment values and authenticated query replay.\<close>

context verification
begin

lemma transcript_read_cons_wp_error:
  "wp_error p.read (s\<lparr>PTranscript := x # xs\<rparr>) = 0"
  unfolding p.read_def protocol_read_def assert_def by (simp add: wpsimps)

lemma merkle_authentication_path_outcome:
  assumes "p.created_tree xs r s0"
    and "length xs = 2 ^ n"
    and "i < length xs"
    and "v = xs ! i"
    and "s0 \<le> s"
    and "Some (h, t) \<in> set_dist (execute
      (p.check_authentication_path (length xs) i v
        (get_authentication_path (length xs) i r)) s)"
  shows "h = value r"
  using p.check_created_tree_outcome[OF assms] by simp

lemma query_f_eval_nth:
  assumes "i < length p.eval_domain"
  shows "p.f_eval ! i = poly p.f (p.eval_domain ! i)"
  using assms unfolding p.f_eval_def by simp

lemma f_powers_nth:
  assumes "k < powers"
  shows "p.f_powers ! k = p.f \<circ>\<^sub>p XP (p.g ^ k)"
  using assms unfolding p.f_powers_def by simp

lemma f_powers_length:
  "length p.f_powers = powers"
  unfolding p.f_powers_def by simp

lemma f_powers_eval:
  assumes "k < powers"
  shows "poly (p.f_powers ! k) x = poly p.f (x * p.g ^ k)"
  using f_powers_nth[OF assms]
  unfolding XP_def
  by (simp add: poly_pcompose poly_monom algebra_simps)

lemma query_cp_eval_nth:
  assumes "i < length p.eval_domain"
  shows "p.cp_eval as ! i = poly (p.cp as p.f_powers) (p.eval_domain ! i)"
  using assms unfolding p.cp_eval_def by simp

lemma powers_scaled_setD:
  assumes "i \<in> set (p.powers_scaled idx)"
  obtains k where "k < powers" and "i = idx + k * scale"
  using assms unfolding p.powers_scaled_def by auto

lemma clength_pos:
  "0 < clength"
proof -
  obtain n where len: "clength * scale = 2 ^ n"
    using p.eval_domain_length_power by blast
  show ?thesis
    using len p.scale_pos by (cases clength) simp_all
qed

lemma max_powers_less_clength:
  "Max (set [0..<powers]) < clength"
proof -
  have "Max (set [0..<powers]) = powers - 1"
    using p.powers_pos by (intro Max_eqI) auto
  also have "... < clength"
    using p.powers_pos p.powers_le_clength by simp
  finally show ?thesis .
qed

lemma index_less_domain:
  "p.index x < clength * scale"
proof -
  have max_le: "Max (set [0..<powers]) < clength"
    by (rule max_powers_less_clength)
  have mod_pos: "0 < clength * scale - Max (set [0..<powers]) * scale"
    using max_le p.scale_pos
    by (simp add: diff_mult_distrib2)
  have idx_lt:
    "p.index x < clength * scale - Max (set [0..<powers]) * scale"
    unfolding p.index_def
    using mod_pos by simp
  have "clength * scale - Max (set [0..<powers]) * scale \<le> clength * scale"
    by simp
  then show ?thesis
    using idx_lt by linarith
qed

lemma index_less_domain_tail:
  assumes "k < powers"
  shows "p.index x + k * scale < clength * scale"
proof -
  have max_le: "Max (set [0..<powers]) < clength"
    by (rule max_powers_less_clength)
  have mod_pos: "0 < clength * scale - Max (set [0..<powers]) * scale"
    using max_le p.scale_pos
    by (simp add: diff_mult_distrib2)
  have idx_lt:
    "p.index x < clength * scale - Max (set [0..<powers]) * scale"
    unfolding p.index_def
    using mod_pos by simp
  have k_le_max: "k * scale \<le> Max (set [0..<powers]) * scale"
  proof (cases "powers = 0")
    case True
    then show ?thesis using assms by simp
  next
    case False
    then have "k \<le> Max (set [0..<powers])"
      using assms by simp
    then show ?thesis by simp
  qed
  have "p.index x + k * scale <
    (clength * scale - Max (set [0..<powers]) * scale) +
      Max (set [0..<powers]) * scale"
    using idx_lt k_le_max by linarith
  also have "... = clength * scale"
    using max_le p.scale_pos
    by (simp add: diff_mult_distrib2)
  finally show ?thesis .
qed

lemma powers_scaled_index_bound:
  assumes "i \<in> set (p.powers_scaled (p.index x))"
  shows "i < clength * scale"
  using assms
  by (auto elim!: powers_scaled_setD intro!: index_less_domain_tail)

lemma f_eval_length:
  "length p.f_eval = clength * scale"
  unfolding p.f_eval_def p.eval_domain_def p.H_def by simp

lemma trace_polynomial_degree_lt_clength:
  "degree p.f < clength"
proof -
  have vals_len: "length vals = clength"
    using p.trace_length by simp
  have G_len: "length p.G = clength"
    unfolding p.G_def by simp
  have deg_le:
    "degree p.f \<le> length (zip p.G vals) - 1"
    unfolding p.f_def by (rule degree_lagrange_interpolation_poly)
  have zip_len: "length (zip p.G vals) = clength"
    using vals_len G_len by simp
  show ?thesis
    using deg_le zip_len p.clength_pos by simp
qed

lemma honest_initial_trace_fri_accumulator_value:
  assumes fv_eq: "fv = map (\<lambda>i. p.f_eval ! i) (p.powers_scaled (p.index x))"
    and l0_eq: "l0 = p.f_eval"
  shows "hd fv = l0 ! p.index x"
proof -
  have range: "[0..<powers] = 0 # [1..<powers]"
    using p.powers_pos by (simp add: upt_conv_Cons)
  have ps:
    "p.powers_scaled (p.index x) =
      p.index x # map (\<lambda>xa. p.index x + xa * scale) [1..<powers]"
    unfolding p.powers_scaled_def using range by simp
  show ?thesis
    using fv_eq l0_eq ps by simp
qed

lemma eval_domain_length:
  "length p.eval_domain = clength * scale"
  unfolding p.eval_domain_def p.H_def by simp

lemma eval_domain_nth:
  assumes "i < clength * scale"
  shows "p.eval_domain ! i = p.h ^ i * shift"
  using assms
  unfolding p.eval_domain_def p.H_def
  by (simp add: mult.commute)

lemma query_f_power_eval_nth:
  assumes k_bound: "k < powers"
    and idx_bound: "idx + k * scale < clength * scale"
  shows
    "p.f_eval ! (idx + k * scale) =
      poly (p.f_powers ! k) (p.h ^ idx * shift)"
proof -
  have eval:
    "p.f_eval ! (idx + k * scale) =
      poly p.f (p.h ^ (idx + k * scale) * shift)"
    using query_f_eval_nth[of "idx + k * scale"] eval_domain_nth[OF idx_bound]
      idx_bound eval_domain_length
    by simp
  have arg:
    "(p.h ^ idx * shift) * p.g ^ k = p.h ^ (idx + k * scale) * shift"
  proof -
    have gpow: "p.g ^ k = p.h ^ (scale * k)"
      using p.domain_alignment by (simp add: power_mult)
    have "(p.h ^ idx * shift) * p.g ^ k =
        p.h ^ idx * p.h ^ (scale * k) * shift"
      using gpow by (simp add: algebra_simps)
    also have "... = p.h ^ (idx + k * scale) * shift"
      by (simp add: power_add algebra_simps mult.commute)
    finally show ?thesis .
  qed
  show ?thesis
    using eval f_powers_eval[OF k_bound, of "p.h ^ idx * shift"] arg
    by simp
qed

lemma honest_query_values_f_powers:
  "map (\<lambda>i. p.f_eval ! i) (p.powers_scaled (p.index x)) =
    map (\<lambda>q. poly q (p.h ^ p.index x * shift)) p.f_powers"
proof (rule nth_equalityI)
  show "length (map (\<lambda>i. p.f_eval ! i) (p.powers_scaled (p.index x))) =
    length (map (\<lambda>q. poly q (p.h ^ p.index x * shift)) p.f_powers)"
    unfolding p.powers_scaled_def using f_powers_length by simp
next
  fix k
  assume k_bound:
    "k < length (map (\<lambda>i. p.f_eval ! i) (p.powers_scaled (p.index x)))"
  then have k_lt: "k < powers"
    unfolding p.powers_scaled_def by simp
  have idx_bound: "p.index x + k * scale < clength * scale"
    by (rule index_less_domain_tail[OF k_lt])
  have left:
    "map (\<lambda>i. p.f_eval ! i) (p.powers_scaled (p.index x)) ! k =
      p.f_eval ! (p.index x + k * scale)"
    using k_lt unfolding p.powers_scaled_def by simp
  have right:
    "map (\<lambda>q. poly q (p.h ^ p.index x * shift)) p.f_powers ! k =
      poly (p.f_powers ! k) (p.h ^ p.index x * shift)"
    using k_lt f_powers_length by simp
  show
    "map (\<lambda>i. p.f_eval ! i) (p.powers_scaled (p.index x)) ! k =
     map (\<lambda>q. poly q (p.h ^ p.index x * shift)) p.f_powers ! k"
    using query_f_power_eval_nth[OF k_lt idx_bound] left right by simp
qed

lemma honest_cp_eval_agrees_lists:
  fixes specs :: "(('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat) list"
    and spec2s :: "(('f list \<Rightarrow> 'f) \<times> nat list) list"
    and pacc :: "'f poly"
    and vacc :: "'f"
  assumes hta: "honest_trace_algebra"
    and idx_bound: "idx < clength * scale"
    and len: "length spec2s = length specs"
    and zip_subset: "set (zip specs spec2s) \<subseteq> set (zip spec spec2)"
    and specs_subset: "set specs \<subseteq> set spec"
    and acc_eq: "vacc = poly pacc (p.h ^ idx * shift)"
  shows
    "fold
      (\<lambda>(a, (c2, roots2)).
        (+) (a * (c2 (map (\<lambda>q. poly q (p.h ^ idx * shift)) p.f_powers) div
          poly (prod (p.g_map roots2)) (p.h ^ idx * shift))))
      (zip as spec2s) vacc =
    poly
      (fold
        (\<lambda>(a, (c, roots, _)).
          (+) (CP a * ((c p.f_powers) div prod (p.g_map roots))))
        (zip as specs) pacc)
      (p.h ^ idx * shift)"
  using len zip_subset specs_subset acc_eq
proof (induction specs arbitrary: as spec2s pacc vacc)
  case Nil
  then have "spec2s = []"
    by simp
  then show ?case
    using Nil.prems(4) by simp
next
  case (Cons s specs')
  obtain c roots d where s_eq: "s = (c, roots, d)"
    by (cases s) auto
  show ?case
  proof (cases spec2s)
    case Nil
    then show ?thesis
      using Cons.prems(1) by simp
  next
    case spec2_Cons: (Cons s2 spec2s')
    then obtain c2 roots2 where s2_eq: "s2 = (c2, roots2)"
      by (cases s2) auto
    have len_tail: "length spec2s' = length specs'"
      using Cons.prems(1) spec2_Cons by simp
    show ?thesis
    proof (cases as)
      case Nil
      then show ?thesis
        using Cons.prems(4) by simp
    next
      case as_Cons: (Cons a as')
      have pair_in:
        "((c, roots, d), (c2, roots2)) \<in> set (zip spec spec2)"
      proof -
        have "(s, s2) \<in> set (zip (s # specs') (s2 # spec2s'))"
          by simp
        moreover have "set (zip (s # specs') (s2 # spec2s')) \<subseteq> set (zip spec spec2)"
          using Cons.prems(2) spec2_Cons by simp
        ultimately have "(s, s2) \<in> set (zip spec spec2)"
          by blast
        then show ?thesis
          using s_eq s2_eq by simp
      qed
      have spec_entry: "(c, roots, d) \<in> set spec"
      proof -
        have "s \<in> set (s # specs')"
          by simp
        then have "s \<in> set spec"
          using Cons.prems(3) by blast
        then show ?thesis
          using s_eq by simp
      qed
      have roots_eq: "roots2 = roots"
        and raw_eq:
          "c2 (map (\<lambda>q. poly q (p.h ^ idx * shift)) p.f_powers) =
            poly (c p.f_powers) (p.h ^ idx * shift)"
        using v.specs_agree[OF pair_in, of p.f_powers "p.h ^ idx * shift"]
        unfolding p.f_powers_def by simp_all
      have quotient_eq:
        "poly ((c p.f_powers) div prod (p.g_map roots)) (p.h ^ idx * shift) =
          poly (c p.f_powers) (p.h ^ idx * shift) div
            poly (prod (p.g_map roots)) (p.h ^ idx * shift)"
        by (rule honest_trace_algebra_quotient_eval[OF hta spec_entry idx_bound])
      have cp_eval: "poly (CP a) (p.h ^ idx * shift) = a"
        by (simp add: CP_def poly_monom)
      have term_eq:
        "a * (c2 (map (\<lambda>q. poly q (p.h ^ idx * shift)) p.f_powers) div
            poly (prod (p.g_map roots2)) (p.h ^ idx * shift)) =
          poly (CP a * ((c p.f_powers) div prod (p.g_map roots)))
            (p.h ^ idx * shift)"
        using roots_eq raw_eq quotient_eq cp_eval by simp
      have acc_step:
        "a * (c2 (map (\<lambda>q. poly q (p.h ^ idx * shift)) p.f_powers) div
            poly (prod (p.g_map roots2)) (p.h ^ idx * shift)) + vacc =
          poly (CP a * ((c p.f_powers) div prod (p.g_map roots)) + pacc)
            (p.h ^ idx * shift)"
        using term_eq Cons.prems(4) by simp
      have tail:
        "fold
          (\<lambda>(a, (c2, roots2)).
            (+) (a * (c2 (map (\<lambda>q. poly q (p.h ^ idx * shift)) p.f_powers) div
              poly (prod (p.g_map roots2)) (p.h ^ idx * shift))))
          (zip as' spec2s')
          (a * (c2 (map (\<lambda>q. poly q (p.h ^ idx * shift)) p.f_powers) div
            poly (prod (p.g_map roots2)) (p.h ^ idx * shift)) + vacc) =
        poly
          (fold
            (\<lambda>(a, (c, roots, _)).
              (+) (CP a * ((c p.f_powers) div prod (p.g_map roots))))
            (zip as' specs')
            (CP a * ((c p.f_powers) div prod (p.g_map roots)) + pacc))
          (p.h ^ idx * shift)"
      proof (rule Cons.IH)
        show "length spec2s' = length specs'"
          using len_tail .
        show "set (zip specs' spec2s') \<subseteq> set (zip spec spec2)"
          using Cons.prems(2) spec2_Cons by auto
        show "set specs' \<subseteq> set spec"
          using Cons.prems(3) by auto
        show "a * (c2 (map (\<lambda>q. poly q (p.h ^ idx * shift)) p.f_powers) /
            poly (prod (p.g_map roots2)) (p.h ^ idx * shift)) + vacc =
          poly (CP a * ((c p.f_powers) div prod (p.g_map roots)) + pacc)
            (p.h ^ idx * shift)"
          using acc_step by simp
      qed
      show ?thesis
        using as_Cons spec2_Cons s_eq s2_eq tail by simp
    qed
  qed
qed

lemma honest_cp_eval_agrees:
  assumes hta: "honest_trace_algebra"
    and idx_bound: "idx < clength * scale"
  shows
    "v.cp_eval as (map (\<lambda>q. poly q (p.h ^ idx * shift)) p.f_powers)
        (p.h ^ idx * shift) =
      poly (p.cp as p.f_powers) (p.h ^ idx * shift)"
  unfolding v.cp_eval_def p.cp_def
  by (rule honest_cp_eval_agrees_lists[OF hta idx_bound])
    (use v.spec2_length in auto)

lemma honest_query_cp_value:
  assumes "honest_trace_valid"
  shows
    "v.cp_eval as (map (\<lambda>i. p.f_eval ! i) (p.powers_scaled (p.index x)))
        (p.h ^ p.index x * shift) =
      poly (p.cp as p.f_powers) (p.h ^ p.index x * shift)"
proof -
  have hta: "honest_trace_algebra"
    using assms unfolding honest_trace_valid_def by simp
  have idx_bound: "p.index x < clength * scale"
    by (rule index_less_domain)
  show ?thesis
    using honest_cp_eval_agrees[OF hta idx_bound, of as]
      honest_query_values_f_powers[of x]
    by simp
qed

lemma cp_eval_index_value:
  "p.cp_eval as ! p.index x =
    poly (p.cp as p.f_powers) (p.h ^ p.index x * shift)"
proof -
  have idx_bound: "p.index x < length p.eval_domain"
    using index_less_domain eval_domain_length by simp
  have "p.cp_eval as ! p.index x =
    poly (p.cp as p.f_powers) (p.eval_domain ! p.index x)"
    by (rule query_cp_eval_nth[OF idx_bound])
  also have "... = poly (p.cp as p.f_powers) (p.h ^ p.index x * shift)"
    using eval_domain_nth[OF index_less_domain[of x]] by simp
  finally show ?thesis .
qed

lemma honest_initial_fri_accumulator_value:
  assumes htv: "honest_trace_valid"
    and as_eq: "as' = as"
    and fv_eq: "fv = map (\<lambda>i. p.f_eval ! i) (p.powers_scaled (p.index x))"
    and l0_eq: "l0 = p.cp_eval as"
  shows
    "v.cp_eval as' fv (p.h ^ p.index x * shift) = l0 ! p.index x"
  using honest_query_cp_value[OF htv, of as x] cp_eval_index_value[of as x]
    as_eq fv_eq l0_eq
  by simp

lemma h_nonzero:
  "p.h \<noteq> 0"
  unfolding p.h_def using p.omega_nonzero_derived by simp

lemma verifier_domain_point_nonzero:
  "((p.h ^ i) * shift) ^ pw \<noteq> 0"
  using h_nonzero p.shift_nonzero by simp

lemma eval_domain_size_pos:
  "0 < clength * scale"
  using maxDegree_less_eval_domain by linarith

lemma h_power_mod_eval_domain:
  "p.h ^ (k mod (clength * scale)) = p.h ^ k"
proof -
  let ?N = "clength * scale"
  have order: "p.h ^ ?N = 1"
    using p.h_order .
  have k_eq: "k = (k div ?N) * ?N + k mod ?N"
    using div_mult_mod_eq[of k ?N] by (simp add: mult.commute)
  have period: "p.h ^ ((k div ?N) * ?N) = 1"
  proof -
    have "p.h ^ ((k div ?N) * ?N) = p.h ^ (?N * (k div ?N))"
      by (simp add: mult.commute)
    also have "... = (p.h ^ ?N) ^ (k div ?N)"
      by (simp only: power_mult)
    also have "... = 1"
      using order by simp
    finally show ?thesis .
  qed
  have "p.h ^ k = p.h ^ ((k div ?N) * ?N + k mod ?N)"
    using k_eq by simp
  also have "... = p.h ^ ((k div ?N) * ?N) * p.h ^ (k mod ?N)"
    by (simp add: power_add)
  also have "... = p.h ^ (k mod ?N)"
    using period by simp
  finally show ?thesis
    by simp
qed

lemma h_half_shift:
  "p.h ^ (k + (clength * scale) div 2) = -(p.h ^ k)"
  using p.h_half_order
  by (simp add: power_add algebra_simps)

lemma mod_mult_right_factor_nat:
  fixes a b c :: nat
  assumes b_pos: "0 < b"
    and c_pos: "0 < c"
  shows "((a mod b) * c) mod (b * c) = (a * c) mod (b * c)"
proof -
  have decomp: "a = a div b * b + a mod b"
    using div_mult_mod_eq[of a b] by simp
  have r_less: "(a mod b) * c < b * c"
    using b_pos c_pos mod_less_divisor[OF b_pos]
    by (simp add: mult_less_mono2)
  have r_le: "(a mod b) * c \<le> a * c"
  proof -
    have "a mod b \<le> a"
      using decomp by linarith
    then show ?thesis
      by simp
  qed
  have dvd_diff: "b * c dvd a * c - (a mod b) * c"
  proof -
    have ac_decomp: "a * c = (a div b) * (b * c) + (a mod b) * c"
    proof -
      have "a * c = (a div b * b + a mod b) * c"
        using decomp by simp
      also have "... = (a div b * b) * c + (a mod b) * c"
        by (simp only: distrib_right)
      also have "... = (a div b) * (b * c) + (a mod b) * c"
        by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have "a * c - (a mod b) * c = (a div b) * (b * c)"
      using ac_decomp by simp
    then show ?thesis by simp
  qed
  have "(a * c) mod (b * c) = (a mod b) * c"
    by (rule mod_nat_eqI[OF r_less r_le dvd_diff])
  then show ?thesis by simp
qed

lemma fri_sibling_domain_round:
  assumes len_pos: "0 < len"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
  shows
    "((p.h ^ ((i + len div 2) mod len)) * shift) ^ pw =
      - (((p.h ^ i) * shift) ^ pw)"
proof -
  let ?N = "clength * scale"
  have pw_pos: "0 < pw"
    using len_pos round eval_domain_size_pos by (cases pw) simp_all
  have half_round: "(len div 2) * pw = ?N div 2"
  proof -
    from even_len obtain k where len_eq: "len = 2 * k"
      by blast
    then have "?N = 2 * (k * pw)"
      using round by simp
    then show ?thesis
      using len_eq by simp
  qed
  have exp_mod:
    "(((i + len div 2) mod len) * pw) mod ?N =
      (i * pw + ?N div 2) mod ?N"
  proof -
    have "(((i + len div 2) mod len) * pw) mod ?N =
        ((i + len div 2) * pw) mod ?N"
      using mod_mult_right_factor_nat[OF len_pos pw_pos, of "i + len div 2"]
        round by simp
    also have "... = (i * pw + ?N div 2) mod ?N"
      using half_round by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have h_exp:
    "p.h ^ (((i + len div 2) mod len) * pw) = -(p.h ^ (i * pw))"
  proof -
    have "p.h ^ (((i + len div 2) mod len) * pw) =
        p.h ^ ((((i + len div 2) mod len) * pw) mod ?N)"
      using h_power_mod_eval_domain[of "((i + len div 2) mod len) * pw"]
      by simp
    also have "... = p.h ^ ((i * pw + ?N div 2) mod ?N)"
      using exp_mod by simp
    also have "... = p.h ^ (i * pw + ?N div 2)"
      using h_power_mod_eval_domain[of "i * pw + ?N div 2"] by simp
    also have "... = -(p.h ^ (i * pw))"
      by (rule h_half_shift)
    finally show ?thesis .
  qed
  have lhs:
    "((p.h ^ ((i + len div 2) mod len)) * shift) ^ pw =
      p.h ^ (((i + len div 2) mod len) * pw) * shift ^ pw"
    by (simp add: power_mult power_mult_distrib)
  have rhs:
    "((p.h ^ i) * shift) ^ pw = p.h ^ (i * pw) * shift ^ pw"
    by (simp add: power_mult power_mult_distrib)
  show ?thesis
    using h_exp by (simp add: power_mult power_mult_distrib)
qed

lemma fri_sibling_domain_at:
  assumes len_pos: "0 < len"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
    and z_eq: "z = ((p.h ^ i) * shift) ^ pw"
    and d_sib:
      "d ! ((i + len div 2) mod len) =
        ((p.h ^ ((i + len div 2) mod len)) * shift) ^ pw"
  shows "d ! ((i + len div 2) mod len) = - z"
  using fri_sibling_domain_round[OF len_pos even_len round, of i] z_eq d_sib
  by simp

lemma fri_next_domain_round:
  assumes half_pos: "0 < len div 2"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
  shows
    "((p.h ^ i) * shift) ^ pw * ((p.h ^ i) * shift) ^ pw =
      ((p.h ^ (i mod (len div 2))) * shift) ^ (pw + pw)"
proof -
  let ?N = "clength * scale"
  have len_pos: "0 < len"
    using half_pos by simp
  have pw_pos: "0 < pw"
    using len_pos round eval_domain_size_pos by (cases pw) simp_all
  have double_pw_pos: "0 < pw + pw"
    using pw_pos by simp
  have double_round: "(len div 2) * (pw + pw) = ?N"
  proof -
    from even_len obtain k where len_eq: "len = 2 * k"
      by blast
    have len_half: "len div 2 = k"
      using len_eq by simp
    have "k * (pw + pw) = 2 * k * pw"
    proof -
      have "k * (pw + pw) = k * pw + k * pw"
        by (simp add: distrib_left)
      also have "... = (k + k) * pw"
        by (simp add: distrib_right)
      also have "... = 2 * k * pw"
        by simp
      finally show ?thesis .
    qed
    moreover have "2 * k * pw = ?N"
      using len_eq round by simp
    ultimately show ?thesis
      using len_half by simp
  qed
  have exp_mod:
    "((i mod (len div 2)) * (pw + pw)) mod ?N =
      (i * (pw + pw)) mod ?N"
  proof -
    have "((i mod (len div 2)) * (pw + pw)) mod ?N =
        ((i mod (len div 2)) * (pw + pw)) mod ((len div 2) * (pw + pw))"
      using double_round by simp
    also have "... = (i * (pw + pw)) mod ((len div 2) * (pw + pw))"
      using mod_mult_right_factor_nat[OF half_pos double_pw_pos, of i]
      by simp
    also have "... = (i * (pw + pw)) mod ?N"
      using double_round by simp
    finally show ?thesis .
  qed
  have h_exp:
    "p.h ^ ((i mod (len div 2)) * (pw + pw)) =
      p.h ^ (i * (pw + pw))"
  proof -
    have "p.h ^ ((i mod (len div 2)) * (pw + pw)) =
        p.h ^ (((i mod (len div 2)) * (pw + pw)) mod ?N)"
      using h_power_mod_eval_domain[of "(i mod (len div 2)) * (pw + pw)"]
      by simp
    also have "... = p.h ^ ((i * (pw + pw)) mod ?N)"
      using exp_mod by simp
    also have "... = p.h ^ (i * (pw + pw))"
      using h_power_mod_eval_domain[of "i * (pw + pw)"] by simp
    finally show ?thesis .
  qed
  show ?thesis
  proof -
    have lhs:
      "((p.h ^ i) * shift) ^ pw * ((p.h ^ i) * shift) ^ pw =
        p.h ^ (i * (pw + pw)) * shift ^ (pw + pw)"
    proof -
      have "((p.h ^ i) * shift) ^ pw * ((p.h ^ i) * shift) ^ pw =
          ((p.h ^ i) * shift) ^ (pw + pw)"
        by (simp add: power_add)
      also have "... = (p.h ^ i) ^ (pw + pw) * shift ^ (pw + pw)"
        by (simp add: power_mult_distrib)
      also have "... = p.h ^ (i * (pw + pw)) * shift ^ (pw + pw)"
        by (simp add: power_mult)
      finally show ?thesis .
    qed
    have rhs:
      "((p.h ^ (i mod (len div 2))) * shift) ^ (pw + pw) =
        p.h ^ ((i mod (len div 2)) * (pw + pw)) * shift ^ (pw + pw)"
      by (simp add: power_mult power_mult_distrib)
    show ?thesis
      using lhs rhs h_exp by simp
  qed
qed

lemma fri_next_domain_at:
  assumes half_pos: "0 < len div 2"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
    and d_i: "d ! i = ((p.h ^ i) * shift) ^ pw"
    and d_next: "d' ! (i mod (len div 2)) = d ! i * d ! i"
  shows
    "d' ! (i mod (len div 2)) =
      ((p.h ^ (i mod (len div 2))) * shift) ^ (pw + pw)"
  using fri_next_domain_round[OF half_pos even_len round, of i] d_i d_next
  by simp

lemma cp_eval_length:
  "length (p.cp_eval as) = clength * scale"
  unfolding p.cp_eval_def using eval_domain_length by simp

lemma f_eval_length_power:
  "\<exists>n. length p.f_eval = 2 ^ n"
  using p.eval_domain_length_power f_eval_length by simp

lemma cp_eval_length_power:
  "\<exists>n. length (p.cp_eval as) = 2 ^ n"
  using p.eval_domain_length_power cp_eval_length by simp

lemma ceil_log_Suc_le_power:
  assumes "d < 2 ^ N"
  shows "ceil_log (Suc d) \<le> N"
proof (cases "d = 0")
  case True
  then show ?thesis
    unfolding ceil_log_def by simp
next
  case False
  then have d_pos: "0 < d"
    by simp
  have "2 ^ floor_log d \<le> d"
    by (rule floor_log_exp2_le[OF d_pos])
  also have "... < 2 ^ N"
    using assms .
  finally have "floor_log d < N"
    by (subst (asm) power_strict_increasing_iff) simp_all
  then show ?thesis
    using False unfolding ceil_log_def by simp
qed

lemma ceil_log_mono:
  assumes "m \<le> n"
  shows "ceil_log m \<le> ceil_log n"
proof (cases "m \<le> 1")
  case True
  then show ?thesis
    unfolding ceil_log_def by simp
next
  case False
  then have m_gt: "1 < m"
    by simp
  then have n_gt: "1 < n"
    using assms by simp
  have "m - 1 \<le> n - 1"
    using assms by simp
  then have "floor_log (m - 1) \<le> floor_log (n - 1)"
    using floor_log_le_iff by blast
  then show ?thesis
    using m_gt n_gt unfolding ceil_log_def by simp
qed

lemma fri_rounds_le_eval_domain_log:
  assumes htv: "honest_trace_valid"
    and cp'_def: "cp' = p.cp as p.f_powers"
    and nrounds_def: "nrounds = ceil_log (degree cp' + 1)"
    and init_len: "length (p.cp_eval as) = 2 ^ N"
  shows "nrounds \<le> N"
proof -
  have "degree cp' \<le> p.maxDegree"
    using composition_degree_from_honest_trace_valid[OF htv, of as] cp'_def by simp
  also have "... < clength * scale"
    by (rule maxDegree_less_eval_domain)
  also have "... = 2 ^ N"
    using init_len cp_eval_length by simp
  finally have "degree cp' < 2 ^ N" .
  then show ?thesis
    using ceil_log_Suc_le_power[of "degree cp'" N]
    unfolding nrounds_def by simp
qed

lemma query_authentication_path_length:
  assumes create_f:
    "Some (f_merkle, s1) \<in> set_dist (execute (p.create p.f_eval) init_state)"
    and i_in: "i \<in> set (p.powers_scaled (p.index x))"
  shows
    "length (get_authentication_path (length p.f_eval) i f_merkle) =
      floor_log (length p.f_eval)"
proof -
  have i_bound: "i < length p.f_eval"
    using i_in unfolding f_eval_length
    by (rule powers_scaled_index_bound)
  then have len_pos: "0 < length p.f_eval"
    by (cases p.f_eval) simp_all
  show ?thesis
    by (rule p.create_get_authentication_path_len[OF create_f len_pos])
      simp
qed

definition query_decommitment_transcript
  where
    "query_decommitment_transcript idx f_merkle \<equiv>
      List.concat (map
        (\<lambda>i. p.f_eval ! i #
          get_authentication_path (length p.f_eval) i f_merkle)
        (p.powers_scaled idx))"

lemma decommit_on_query_step_transcript:
  assumes step:
    "Some (x, t) \<in>
      set_dist (execute
        (do {
          p.send (p.f_eval ! i);
          mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)
        }) s)"
  shows
    "x = () \<and>
     PTranscript t =
       rev (p.f_eval ! i #
         get_authentication_path (length p.f_eval) i f_merkle) @ PTranscript s"
proof -
  from step obtain u where
    send_leaf:
      "Some ((), u) \<in> set_dist (execute (p.send (p.f_eval ! i)) s)"
    and send_path:
      "Some (x, t) \<in>
        set_dist (execute
          (mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)) u)"
    by (auto elim!: p.set_dist_bindE)
  have x_unit: "x = ()"
    by (cases x) simp
  have path_unit:
    "Some ((), t) \<in>
      set_dist (execute
        (mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)) u)"
    using send_path x_unit by simp
  have tr_u: "PTranscript u = p.f_eval ! i # PTranscript s"
    using p.send_outcome[OF send_leaf] by simp
  have tr_t:
    "PTranscript t =
      rev (get_authentication_path (length p.f_eval) i f_merkle) @ PTranscript u"
    using p.mfold2_send_outcome[OF path_unit] by simp
  show ?thesis
    using x_unit tr_u tr_t by simp
qed

lemma decommit_on_query_mmap_transcript:
  assumes outcome:
    "Some (qouts, t) \<in>
      set_dist (execute (mmap (p.decommit_on_query idx f_merkle)) s)"
  shows
    "PTranscript t =
      rev (query_decommitment_transcript idx f_merkle) @ PTranscript s"
proof -
  have aux:
    "\<And>qs qouts t s. Some (qouts, t) \<in>
        set_dist (execute
          (mmap
            (map
              (\<lambda>i. do {
                p.send (p.f_eval ! i);
                mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)
              })
              qs)) s) \<Longrightarrow>
      PTranscript t =
        rev (List.concat (map
          (\<lambda>i. p.f_eval ! i #
            get_authentication_path (length p.f_eval) i f_merkle)
          qs)) @ PTranscript s"
  proof -
    fix qs qouts t s
    assume outcome_qs:
      "Some (qouts, t) \<in>
        set_dist (execute
          (mmap
            (map
              (\<lambda>i. do {
                p.send (p.f_eval ! i);
                mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)
              })
              qs)) s)"
    then show
      "PTranscript t =
        rev (List.concat (map
          (\<lambda>i. p.f_eval ! i #
            get_authentication_path (length p.f_eval) i f_merkle)
          qs)) @ PTranscript s"
    proof (induction qs arbitrary: qouts t s)
    case Nil
    then show ?case by simp
  next
    case (Cons i qs)
    from Cons.prems obtain u0 u qouts' where
      send_leaf:
        "Some ((), u0) \<in> set_dist (execute (p.send (p.f_eval ! i)) s)"
      and send_path:
        "Some ((), u) \<in>
          set_dist (execute
            (mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle))
            u0)"
      and tail:
        "Some (qouts', t) \<in>
          set_dist (execute
            (mmap
              (map
                (\<lambda>i. do {
                  p.send (p.f_eval ! i);
                  mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)
                })
                qs)) u)"
      by (auto elim!: p.set_dist_bindE)
    have head_tr:
      "PTranscript u =
        rev (p.f_eval ! i #
          get_authentication_path (length p.f_eval) i f_merkle) @ PTranscript s"
    proof -
      have tr_u0: "PTranscript u0 = p.f_eval ! i # PTranscript s"
        using p.send_outcome[OF send_leaf] by simp
      have tr_u:
        "PTranscript u =
          rev (get_authentication_path (length p.f_eval) i f_merkle) @ PTranscript u0"
        using p.mfold2_send_outcome[OF send_path] by simp
      show ?thesis
        using tr_u0 tr_u by simp
    qed
    have tail_tr:
      "PTranscript t =
        rev (List.concat (map
          (\<lambda>i. p.f_eval ! i #
            get_authentication_path (length p.f_eval) i f_merkle)
          qs)) @ PTranscript u"
      using Cons.IH[OF tail] .
    show ?case
      using head_tr tail_tr by simp
    qed
  qed
  show ?thesis
    using aux[OF outcome[unfolded p.decommit_on_query_def]]
    unfolding query_decommitment_transcript_def .
qed

lemma decommit_on_query_mmap_state:
  assumes outcome:
    "Some (qouts, t) \<in>
      set_dist (execute (mmap (p.decommit_on_query idx f_merkle)) s)"
  shows "PState t = foldl concat (PState s) (query_decommitment_transcript idx f_merkle)"
proof -
  have aux:
    "\<And>qs qouts t s. Some (qouts, t) \<in>
        set_dist (execute
          (mmap
            (map
              (\<lambda>i. do {
                p.send (p.f_eval ! i);
                mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)
              })
              qs)) s) \<Longrightarrow>
      PState t =
        foldl concat (PState s)
          (List.concat (map
            (\<lambda>i. p.f_eval ! i #
              get_authentication_path (length p.f_eval) i f_merkle)
            qs))"
  proof -
    fix qs qouts t s
    assume outcome_qs:
      "Some (qouts, t) \<in>
        set_dist (execute
          (mmap
            (map
              (\<lambda>i. do {
                p.send (p.f_eval ! i);
                mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)
              })
              qs)) s)"
    then show
      "PState t =
        foldl concat (PState s)
          (List.concat (map
            (\<lambda>i. p.f_eval ! i #
              get_authentication_path (length p.f_eval) i f_merkle)
            qs))"
    proof (induction qs arbitrary: qouts t s)
      case Nil
      then show ?case by simp
    next
      case (Cons i qs)
      from Cons.prems obtain u0 u qouts' where
        send_leaf:
          "Some ((), u0) \<in> set_dist (execute (p.send (p.f_eval ! i)) s)"
        and send_path:
          "Some ((), u) \<in>
            set_dist (execute
              (mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle))
              u0)"
        and tail:
          "Some (qouts', t) \<in>
            set_dist (execute
              (mmap
                (map
                  (\<lambda>i. do {
                    p.send (p.f_eval ! i);
                    mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)
                  })
                  qs)) u)"
        by (auto elim!: p.set_dist_bindE)
      have head_state:
        "PState u =
          foldl concat (PState s)
            (p.f_eval ! i # get_authentication_path (length p.f_eval) i f_merkle)"
      proof -
        have st_u0: "PState u0 = concat (PState s) (p.f_eval ! i)"
          using p.send_outcome[OF send_leaf] by simp
        show ?thesis
          using p.mfold2_send_outcome[OF send_path] st_u0 by simp
      qed
      have tail_state:
        "PState t =
          foldl concat (PState u)
            (List.concat (map
              (\<lambda>i. p.f_eval ! i #
                get_authentication_path (length p.f_eval) i f_merkle)
              qs))"
        using Cons.IH[OF tail] .
      show ?case
        using head_state tail_state by simp
    qed
  qed
  show ?thesis
    using aux[OF outcome[unfolded p.decommit_on_query_def]]
    unfolding query_decommitment_transcript_def .
qed

lemma prover_query_decommitment_transcript_in_replay_state:
  assumes final_send:
    "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    and random_idx:
      "Some (idx, s7) \<in> set_dist (execute p.receive_query_index_challenge s_final)"
    and query_decommit:
      "Some (qouts, s8) \<in>
        set_dist (execute (mmap (p.decommit_on_query idx' f_merkle)) s7)"
    and fri_decommit:
      "Some (fri_idx, s9) \<in>
        set_dist (execute
          (mfold idx' (p.decommit_on_fri_layers (butlast (zip ls ms)))) s8)"
    and prover_state_eq: "prover_state = s9"
    and replay: "replay_state = verifier_replay_state prover_state"
  obtains rest where
    "PTranscript replay_state =
      rev (PTranscript s6) @ [hd (last ls)] @
        query_decommitment_transcript idx' f_merkle @ rest"
proof -
  have final_tr:
    "PTranscript s_final = hd (last ls) # PTranscript s6"
    using p.send_outcome[OF final_send] by simp
  have s7_tr: "PTranscript s7 = PTranscript s_final"
    using receive_query_index_challenge_preserves_transcript[OF random_idx] .
  have s8_tr:
    "PTranscript s8 =
      rev (query_decommitment_transcript idx' f_merkle) @ PTranscript s7"
    using decommit_on_query_mmap_transcript[OF query_decommit] .
  have s8_s9: "transcript_extends s9 s8"
    by (rule mfold_transcript_extends[OF fri_decommit])
      (rule decommit_on_fri_layers_step_transcript_extends)
  then obtain more where more:
    "PTranscript s9 = more @ PTranscript s8"
    unfolding transcript_extends_def by blast
  have prover_tr:
    "PTranscript prover_state =
      more @ rev (query_decommitment_transcript idx' f_merkle) @
        hd (last ls) # PTranscript s6"
    using more s8_tr s7_tr final_tr prover_state_eq by simp
  have replay_tr:
    "PTranscript replay_state =
      rev (PTranscript s6) @ [hd (last ls)] @
        query_decommitment_transcript idx' f_merkle @ rev more"
    using prover_tr replay
    unfolding verifier_replay_state_def by simp
  show ?thesis
    by (rule that[OF replay_tr])
qed

lemma honest_query_decommitment_list_no_failure:
  assumes created: "p.created_tree p.f_eval f_merkle s0"
    and len_pow: "length p.f_eval = 2 ^ n"
    and ext: "s0 \<le> s"
    and paths:
      "\<And>i. i \<in> set (p.powers_scaled (p.index x)) \<Longrightarrow>
        length (get_authentication_path (length p.f_eval) i f_merkle) =
          floor_log (length p.f_eval)"
    and root: "fr = value f_merkle"
  shows
    "None \<notin> dom (dist (execute
      (mmap (v.check_decommit_on_query fr (p.index x)))
      (s\<lparr>
        PTranscript :=
          query_decommitment_transcript (p.index x) f_merkle @ rest
      \<rparr>)))"
proof -
  have check_eq:
    "v.check_decommit_on_query fr (p.index x) =
      map
        (\<lambda>i. do {
          qh \<leftarrow> p.read;
          let len = scale * clength;
          qh_path \<leftarrow> ntimes p.read (floor_log len);
          ap \<leftarrow> p.check_authentication_path len i qh qh_path;
          assert (ap = fr);
          return qh
        })
        (p.powers_scaled (p.index x))"
    unfolding v.check_decommit_on_query_def p.powers_scaled_def by simp
  define qs where "qs = p.powers_scaled (p.index x)"
  have list_nf:
    "\<And>qs rest s.
      set qs \<subseteq> set (p.powers_scaled (p.index x)) \<Longrightarrow>
      s0 \<le> s \<Longrightarrow>
      None \<notin> dom (dist (execute
        (mmap
          (map
            (\<lambda>i. do {
              qh \<leftarrow> p.read;
              let len = scale * clength;
              qh_path \<leftarrow> ntimes p.read (floor_log len);
              ap \<leftarrow> p.check_authentication_path len i qh qh_path;
              assert (ap = fr);
              return qh
            })
            qs))
        (s\<lparr>
          PTranscript :=
            List.concat (map
              (\<lambda>i. p.f_eval ! i #
                get_authentication_path (length p.f_eval) i f_merkle)
              qs) @ rest
        \<rparr>)))"
  proof -
    fix qs rest s
    assume qs_subset: "set qs \<subseteq> set (p.powers_scaled (p.index x))"
      and s0_s: "s0 \<le> s"
    then show
      "None \<notin> dom (dist (execute
        (mmap
          (map
            (\<lambda>i. do {
              qh \<leftarrow> p.read;
              let len = scale * clength;
              qh_path \<leftarrow> ntimes p.read (floor_log len);
              ap \<leftarrow> p.check_authentication_path len i qh qh_path;
              assert (ap = fr);
              return qh
            })
            qs))
        (s\<lparr>
          PTranscript :=
            List.concat (map
              (\<lambda>i. p.f_eval ! i #
                get_authentication_path (length p.f_eval) i f_merkle)
              qs) @ rest
        \<rparr>)))"
    proof (induction qs arbitrary: rest s)
      case Nil
      then show ?case by simp
    next
      case (Cons i qs)
    have i_in: "i \<in> set (p.powers_scaled (p.index x))"
      using Cons.prems(1) by simp
    let ?path = "get_authentication_path (length p.f_eval) i f_merkle"
    let ?msg = "p.f_eval ! i # ?path"
    let ?tail =
      "List.concat (map
        (\<lambda>i. p.f_eval ! i #
          get_authentication_path (length p.f_eval) i f_merkle)
        qs) @ rest"
    have i_bound: "i < length p.f_eval"
      using i_in unfolding f_eval_length
      by (rule powers_scaled_index_bound)
    have path_len:
      "length ?path = floor_log (length p.f_eval)"
      using paths[OF i_in] .
    have step_nf:
      "None \<notin> dom (dist (execute
        (do {
          qh \<leftarrow> p.read;
          let len = scale * clength;
          qh_path \<leftarrow> ntimes p.read (floor_log len);
          ap \<leftarrow> p.check_authentication_path len i qh qh_path;
          assert (ap = fr);
          return qh
        })
        (s\<lparr>PTranscript := ?msg @ ?tail\<rparr>)))"
      using p.honest_query_decommitment_no_failure[
        OF created len_pow i_bound refl Cons.prems(2) path_len root,
        of ?tail]
      unfolding f_eval_length by (simp add: mult.commute Let_def)
    let ?step =
      "do {
        qh \<leftarrow> p.read;
        let len = scale * clength;
        qh_path \<leftarrow> ntimes p.read (floor_log len);
        ap \<leftarrow> p.check_authentication_path len i qh qh_path;
        assert (ap = fr);
        return qh
      }"
    let ?tail_m =
      "mmap
        (map
          (\<lambda>i. do {
            qh \<leftarrow> p.read;
            let len = scale * clength;
            qh_path \<leftarrow> ntimes p.read (floor_log len);
            ap \<leftarrow> p.check_authentication_path len i qh qh_path;
            assert (ap = fr);
            return qh
          })
          qs)"
    have case_eq:
      "?case =
        (None \<notin> dom (dist (execute
          (?step \<bind> (\<lambda>qh. ?tail_m \<bind> (\<lambda>qhs. return (qh # qhs))))
          (s\<lparr>PTranscript := ?msg @ ?tail\<rparr>))))"
      by (simp add: Let_def)
    show ?case
      unfolding case_eq
    proof (rule no_failure_bindI[OF step_nf])
      fix qh t
      assume step:
        "Some (qh, t) \<in> set_dist (execute
          (do {
            qh \<leftarrow> p.read;
            let len = scale * clength;
            qh_path \<leftarrow> ntimes p.read (floor_log len);
            ap \<leftarrow> p.check_authentication_path len i qh qh_path;
            assert (ap = fr);
            return qh
          })
          (s\<lparr>PTranscript := ?msg @ ?tail\<rparr>))"
      have head_state: "s0 \<le> t \<and> PTranscript t = ?tail"
      proof -
        from step obtain r u path u' ap u'' u''' where
          read_leaf:
            "Some (r, u) \<in> set_dist (execute p.read (s\<lparr>PTranscript := ?msg @ ?tail\<rparr>))"
          and read_path:
            "Some (path, u') \<in>
              set_dist (execute (ntimes p.read (floor_log (scale * clength))) u)"
          and check:
            "Some (ap, u'') \<in>
              set_dist (execute (p.check_authentication_path (scale * clength) i r path) u')"
          and assert_ok:
            "Some ((), u''') \<in> set_dist (execute (assert (ap = fr)) u'')"
          and ret:
            "Some (qh, t) \<in> set_dist (execute (return r) u''')"
          by (auto simp: Let_def elim!: p.set_dist_bindE)
        have read_start_eq:
          "s\<lparr>PTranscript := ?msg @ ?tail\<rparr> =
            s\<lparr>PTranscript := p.f_eval ! i # (?path @ ?tail)\<rparr>"
          by simp
        have read_leaf_replay:
          "r = p.f_eval ! i \<and>
           u = s\<lparr>
             PState := concat (PState s) (p.f_eval ! i),
             PTranscript := ?path @ ?tail\<rparr>"
          using p.read_cons_outcome[OF read_leaf[unfolded read_start_eq]] by simp
        have r_eq: "r = p.f_eval ! i"
          using read_leaf_replay by simp
        have read_leaf_res:
          "u = s\<lparr>
            PState := concat (PState s) (p.f_eval ! i),
            PTranscript := ?path @ ?tail\<rparr>"
          using read_leaf_replay by simp
        have u_base:
          "u =
            (s\<lparr>PState := concat (PState s) (p.f_eval ! i)\<rparr>)
              \<lparr>PTranscript := ?path @ ?tail\<rparr>"
          using read_leaf_res by simp
        have scale_len: "scale * clength = length p.f_eval"
          using f_eval_length by (simp add: mult.commute)
        have path_replay:
          "path = ?path \<and>
           u' =
             (s\<lparr>PState := concat (PState s) (p.f_eval ! i)\<rparr>)
               \<lparr>
                 PState :=
                   foldl concat
                     (concat (PState s) (p.f_eval ! i))
                     ?path,
                 PTranscript := ?tail
               \<rparr>"
          using p.ntimes_read_prefix_outcome[
            OF read_path[unfolded scale_len path_len[symmetric] u_base]]
          by simp
        have path_eq: "path = ?path"
          using path_replay by simp
        have path_res:
          "u' =
            (s\<lparr>PState := concat (PState s) (p.f_eval ! i)\<rparr>)
              \<lparr>
                PState :=
                  foldl concat
                    (concat (PState s) (p.f_eval ! i))
                    ?path,
                PTranscript := ?tail
              \<rparr>"
          using path_replay by simp
        have s0_u': "s0 \<le> u'"
          using Cons.prems path_res
          unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
        have u'_u'': "u' \<le> u''"
          using p.check_created_tree_outcome[
            OF created len_pow i_bound refl s0_u'
              check[unfolded scale_len r_eq path_eq]]
          unfolding root by simp
        have check_transcript: "PTranscript u'' = PTranscript u'"
          using p.check_authentication_path_preserves_channel(2)[OF check] .
        have assert_state: "u''' = u''"
          using assert_ok unfolding assert_def
          by (cases "ap = fr")
            (auto simp: return.rep_eq dist_return_def throw.rep_eq dist_throw_def
              dist_delta_dist delta_map_def set_dist_def)
        have ret_state: "t = u'''"
          using ret by simp
        have u''_t: "u'' \<le> t"
          unfolding assert_state[symmetric] ret_state
          unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
        have t_transcript: "PTranscript t = ?tail"
          using path_res check_transcript assert_state ret_state by simp
        show ?thesis
        proof
          show "s0 \<le> t"
            using s0_u' u'_u'' u''_t
            unfolding less_eq_hash_ext_def less_eq_fmap_def
            by metis
          show "PTranscript t = ?tail"
            using t_transcript .
        qed
      qed
      have s0_t: "s0 \<le> t"
        using head_state by simp
      have t_transcript: "PTranscript t = ?tail"
        using head_state by simp
      have tail_nf_start:
        "None \<notin> dom (dist (execute ?tail_m (t\<lparr>PTranscript := ?tail\<rparr>)))"
        using Cons.IH[of t rest] Cons.prems(1) s0_t by simp
      have t_update: "t\<lparr>PTranscript := ?tail\<rparr> = t"
        using t_transcript by simp
      have tail_nf: "None \<notin> dom (dist (execute ?tail_m t))"
        using tail_nf_start unfolding t_update .
      show "None \<notin> dom (dist (execute (?tail_m \<bind> (\<lambda>qhs. return (qh # qhs))) t))"
        by (rule no_failure_bindI[OF tail_nf]) simp
    qed
    qed
  qed
  show ?thesis
    using list_nf[of "p.powers_scaled (p.index x)" s rest] ext
    unfolding query_decommitment_transcript_def check_eq qs_def by simp
qed

lemma honest_query_decommitment_replay_no_failure:
  assumes create_f:
      "Some (f_merkle, s0) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and ext: "s0 \<le> s"
    and root: "fr = value f_merkle"
    and transcript:
      "PTranscript s =
        query_decommitment_transcript (p.index x) f_merkle @ rest"
  shows
    "None \<notin> dom (dist (execute
      (mmap (v.check_decommit_on_query fr (p.index x))) s))"
proof -
  have created: "p.created_tree p.f_eval f_merkle s0"
    using p.create_outcome[OF create_f] by simp
  from f_eval_length_power obtain n where len_pow: "length p.f_eval = 2 ^ n"
    by blast
  have paths:
    "\<And>i. i \<in> set (p.powers_scaled (p.index x)) \<Longrightarrow>
      length (get_authentication_path (length p.f_eval) i f_merkle) =
        floor_log (length p.f_eval)"
    using query_authentication_path_length[OF create_f] by blast
  have nf:
    "None \<notin> dom (dist (execute
      (mmap (v.check_decommit_on_query fr (p.index x)))
      (s\<lparr>
        PTranscript :=
          query_decommitment_transcript (p.index x) f_merkle @ rest
      \<rparr>)))"
    by (rule honest_query_decommitment_list_no_failure[
        OF created len_pow ext paths root])
  have update:
    "s\<lparr>PTranscript :=
      query_decommitment_transcript (p.index x) f_merkle @ rest\<rparr> = s"
    using transcript by simp
  show ?thesis
    using nf unfolding update .
qed

lemma honest_query_decommitment_replay_outcome:
  assumes paths:
    "\<And>i. i \<in> set (p.powers_scaled idx) \<Longrightarrow>
      length (get_authentication_path (length p.f_eval) i f_merkle) =
        floor_log (length p.f_eval)"
    and outcome:
      "Some (fv, t) \<in>
        set_dist (execute
          (mmap (v.check_decommit_on_query fr idx))
          (s\<lparr>PTranscript := query_decommitment_transcript idx f_merkle @ rest\<rparr>))"
	  shows
	    "fv = map (\<lambda>i. p.f_eval ! i) (p.powers_scaled idx) \<and>
	     PTranscript t = rest \<and>
	     PState t = foldl concat (PState s) (query_decommitment_transcript idx f_merkle) \<and>
	     s\<lparr>PTranscript := query_decommitment_transcript idx f_merkle @ rest\<rparr> \<le> t"
proof -
  have check_eq:
    "v.check_decommit_on_query fr idx =
      map
        (\<lambda>i. do {
          qh \<leftarrow> p.read;
          let len = scale * clength;
          qh_path \<leftarrow> ntimes p.read (floor_log len);
          ap \<leftarrow> p.check_authentication_path len i qh qh_path;
          assert (ap = fr);
          return qh
        })
        (p.powers_scaled idx)"
    unfolding v.check_decommit_on_query_def p.powers_scaled_def by simp
  have list_out:
    "\<And>qs fv t s rest.
      set qs \<subseteq> set (p.powers_scaled idx) \<Longrightarrow>
      Some (fv, t) \<in>
        set_dist (execute
          (mmap
            (map
              (\<lambda>i. do {
                qh \<leftarrow> p.read;
                let len = scale * clength;
                qh_path \<leftarrow> ntimes p.read (floor_log len);
                ap \<leftarrow> p.check_authentication_path len i qh qh_path;
                assert (ap = fr);
                return qh
              })
              qs))
          (s\<lparr>
            PTranscript :=
              List.concat (map
                (\<lambda>i. p.f_eval ! i #
                  get_authentication_path (length p.f_eval) i f_merkle)
                qs) @ rest
          \<rparr>)) \<Longrightarrow>
		      fv = map (\<lambda>i. p.f_eval ! i) qs \<and>
		      PTranscript t = rest \<and>
		      PState t =
		        foldl concat (PState s)
		          (List.concat (map
		            (\<lambda>i. p.f_eval ! i #
		              get_authentication_path (length p.f_eval) i f_merkle)
		            qs)) \<and>
		      s\<lparr>
		        PTranscript :=
	          List.concat (map
            (\<lambda>i. p.f_eval ! i #
              get_authentication_path (length p.f_eval) i f_merkle)
            qs) @ rest
      \<rparr> \<le> t"
  proof -
    fix qs fv t s rest
    assume qs_subset: "set qs \<subseteq> set (p.powers_scaled idx)"
      and outcome_qs:
        "Some (fv, t) \<in>
          set_dist (execute
            (mmap
              (map
                (\<lambda>i. do {
                  qh \<leftarrow> p.read;
                  let len = scale * clength;
                  qh_path \<leftarrow> ntimes p.read (floor_log len);
                  ap \<leftarrow> p.check_authentication_path len i qh qh_path;
                  assert (ap = fr);
                  return qh
                })
                qs))
            (s\<lparr>
              PTranscript :=
                List.concat (map
                  (\<lambda>i. p.f_eval ! i #
                    get_authentication_path (length p.f_eval) i f_merkle)
                  qs) @ rest
            \<rparr>))"
    then show
		      "fv = map (\<lambda>i. p.f_eval ! i) qs \<and>
		       PTranscript t = rest \<and>
		       PState t =
		         foldl concat (PState s)
		           (List.concat (map
		             (\<lambda>i. p.f_eval ! i #
		               get_authentication_path (length p.f_eval) i f_merkle)
		             qs)) \<and>
		       s\<lparr>
		         PTranscript :=
	           List.concat (map
             (\<lambda>i. p.f_eval ! i #
               get_authentication_path (length p.f_eval) i f_merkle)
             qs) @ rest
       \<rparr> \<le> t"
    proof (induction qs arbitrary: fv t s rest)
      case Nil
      then show ?case
        unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    next
      case (Cons i qs)
      let ?path = "get_authentication_path (length p.f_eval) i f_merkle"
      let ?msg = "p.f_eval ! i # ?path"
      let ?tail =
        "List.concat (map
          (\<lambda>i. p.f_eval ! i #
            get_authentication_path (length p.f_eval) i f_merkle)
          qs) @ rest"
      let ?start = "s\<lparr>PTranscript := ?msg @ ?tail\<rparr>"
      let ?step =
        "do {
          qh \<leftarrow> p.read;
          let len = scale * clength;
          qh_path \<leftarrow> ntimes p.read (floor_log len);
          ap \<leftarrow> p.check_authentication_path len i qh qh_path;
          assert (ap = fr);
          return qh
        }"
      let ?tail_m =
        "mmap
          (map
            (\<lambda>i. do {
              qh \<leftarrow> p.read;
              let len = scale * clength;
              qh_path \<leftarrow> ntimes p.read (floor_log len);
              ap \<leftarrow> p.check_authentication_path len i qh qh_path;
              assert (ap = fr);
              return qh
            })
            qs)"
      have cons_out:
        "Some (fv, t) \<in>
          set_dist (execute
            (?step \<bind> (\<lambda>qh. ?tail_m \<bind> (\<lambda>fv_tail. return (qh # fv_tail))))
            ?start)"
        using Cons.prems(2) by simp
      from cons_out obtain qh u where
        head:
          "Some (qh, u) \<in> set_dist (execute ?step ?start)"
        and tail_bind:
          "Some (fv, t) \<in>
            set_dist (execute (?tail_m \<bind> (\<lambda>fv_tail. return (qh # fv_tail))) u)"
      proof -
        show ?thesis
          using cons_out
        proof (rule p.set_dist_bindE)
          fix qh u
          assume head:
            "Some (qh, u) \<in> set_dist (execute ?step ?start)"
            and tail_bind:
              "Some (fv, t) \<in>
                set_dist (execute
                  (?tail_m \<bind> (\<lambda>fv_tail. return (qh # fv_tail))) u)"
          show ?thesis
            by (rule that[OF head tail_bind])
        qed
      qed
      from tail_bind obtain fv_tail u_tail where
        tail0:
          "Some (fv_tail, u_tail) \<in> set_dist (execute ?tail_m u)"
        and ret_tail:
          "Some (fv, t) \<in> set_dist (execute (return (qh # fv_tail)) u_tail)"
      proof -
        show ?thesis
          using tail_bind
        proof (rule p.set_dist_bindE)
          fix fv_tail u_tail
          assume tail0:
            "Some (fv_tail, u_tail) \<in> set_dist (execute ?tail_m u)"
            and ret_tail:
              "Some (fv, t) \<in>
                set_dist (execute (return (qh # fv_tail)) u_tail)"
          show ?thesis
            by (rule that[OF tail0 ret_tail])
        qed
      qed
      have ret_tail_res: "fv = qh # fv_tail \<and> t = u_tail"
        using ret_tail by simp
      have tail:
        "Some (fv_tail, t) \<in> set_dist (execute ?tail_m u)"
        using tail0 ret_tail_res by simp
      have fv_eq: "fv = qh # fv_tail"
        using ret_tail_res by simp
      have i_in: "i \<in> set (p.powers_scaled idx)"
        using Cons.prems(1) by simp
      have path_len:
        "length ?path = floor_log (scale * clength)"
        using paths[OF i_in] f_eval_length by (simp add: mult.commute)
      from head obtain qh_path ap s1 s2 s3 s4 where
        read_leaf: "Some (qh, s1) \<in> set_dist (execute p.read ?start)"
        and read_path:
          "Some (qh_path, s2) \<in>
            set_dist (execute (ntimes p.read (floor_log (scale * clength))) s1)"
        and check:
          "Some (ap, s3) \<in>
            set_dist (execute
              (p.check_authentication_path (scale * clength) i qh qh_path) s2)"
        and assert_ok:
          "Some ((), s4) \<in> set_dist (execute (assert (ap = fr)) s3)"
        and ret: "Some (qh, u) \<in> set_dist (execute (return qh) s4)"
        by (auto simp: Let_def elim!: p.set_dist_bindE)
      have leaf_res:
        "qh = p.f_eval ! i \<and>
         s1 = s\<lparr>
           PState := concat (PState s) (p.f_eval ! i),
           PTranscript := ?path @ ?tail\<rparr>"
      proof -
        have start_eq:
          "?start =
            s\<lparr>PTranscript := p.f_eval ! i # (?path @ ?tail)\<rparr>"
          by simp
        show ?thesis
          using p.read_cons_outcome[OF read_leaf[unfolded start_eq]] by simp
      qed
      let ?s_leaf = "s\<lparr>PState := concat (PState s) (p.f_eval ! i)\<rparr>"
      have s1_eq: "s1 = ?s_leaf\<lparr>PTranscript := ?path @ ?tail\<rparr>"
        using leaf_res by simp
      have path_res:
        "qh_path = ?path \<and>
         s2 = ?s_leaf\<lparr>
           PState := foldl concat (PState ?s_leaf) ?path,
           PTranscript := ?tail\<rparr>"
        using p.ntimes_read_prefix_outcome[
          OF read_path[unfolded path_len[symmetric] s1_eq]]
        by simp
      have s3_tr: "PTranscript s3 = ?tail"
        using p.check_authentication_path_preserves_channel(2)[OF check] path_res
        by simp
	      have s4_tr: "PTranscript s4 = ?tail"
	        using assert_outcomeD(2)[OF assert_ok] s3_tr by simp
		      have u_eq: "u = s4"
		        using ret by simp
		      have u_tr: "PTranscript u = ?tail"
		        using s4_tr u_eq by simp
	      have u_state:
	        "PState u = foldl concat (PState s) ?msg"
	      proof -
	        have s3_state: "PState s3 = PState s2"
	          using p.check_authentication_path_preserves_channel(1)[OF check] .
	        have s4_state: "PState s4 = PState s3"
	          using assert_outcomeD(2)[OF assert_ok] by simp
	        show ?thesis
	          using leaf_res path_res s3_state s4_state u_eq by simp
	      qed
      have start_u: "?start \<le> u"
      proof -
        have "?start \<le> s1"
          using read_leaf by (rule read_hash_extends)
        moreover have "s1 \<le> s2"
          using read_path by (rule ntimes_read_hash_extends)
        moreover have "s2 \<le> s3"
          using check by (rule check_authentication_path_hash_extends)
        moreover have "s3 \<le> s4"
          using assert_ok by (rule assert_hash_extends)
        moreover have "s4 \<le> u"
          using u_eq p.hash_ext_refl by simp
        ultimately show ?thesis
          by (meson p.hash_ext_trans)
      qed
      have u_update: "u\<lparr>PTranscript := ?tail\<rparr> = u"
        using u_tr by simp
      have tail_start:
        "Some (fv_tail, t) \<in>
          set_dist (execute ?tail_m (u\<lparr>PTranscript := ?tail\<rparr>))"
        using tail unfolding u_update .
		      have tail_out:
		        "fv_tail = map (\<lambda>i. p.f_eval ! i) qs \<and>
		         PTranscript t = rest \<and>
		         PState t =
		           foldl concat (PState u)
		             (List.concat (map
		               (\<lambda>i. p.f_eval ! i #
		                 get_authentication_path (length p.f_eval) i f_merkle)
		               qs)) \<and>
		         u\<lparr>PTranscript := ?tail\<rparr> \<le> t"
      proof (rule Cons.IH)
        show "set qs \<subseteq> set (p.powers_scaled idx)"
          using Cons.prems(1) by simp
        show "Some (fv_tail, t) \<in> set_dist (execute ?tail_m
          (u\<lparr>PTranscript := ?tail\<rparr>))"
          using tail_start .
      qed
	      have start_t: "?start \<le> t"
	        using start_u tail_out unfolding u_update by (meson p.hash_ext_trans)
		      show ?case
		        using fv_eq leaf_res tail_out start_t u_state by simp
    qed
  qed
  have outcome':
    "Some (fv, t) \<in>
      set_dist (execute
        (mmap
          (map
            (\<lambda>i. do {
              qh \<leftarrow> p.read;
              let len = scale * clength;
              qh_path \<leftarrow> ntimes p.read (floor_log len);
              ap \<leftarrow> p.check_authentication_path len i qh qh_path;
              assert (ap = fr);
              return qh
            })
            (p.powers_scaled idx)))
        (s\<lparr>
          PTranscript :=
            List.concat (map
              (\<lambda>i. p.f_eval ! i #
                get_authentication_path (length p.f_eval) i f_merkle)
              (p.powers_scaled idx)) @ rest
        \<rparr>))"
    using outcome
    unfolding check_eq query_decommitment_transcript_def by simp
	  have result:
		    "fv = map (\<lambda>i. p.f_eval ! i) (p.powers_scaled idx) \<and>
		     PTranscript t = rest \<and>
		     PState t =
		       foldl concat (PState s)
		         (List.concat (map
		           (\<lambda>i. p.f_eval ! i #
		             get_authentication_path (length p.f_eval) i f_merkle)
		           (p.powers_scaled idx))) \<and>
		     s\<lparr>
	       PTranscript :=
	         List.concat (map
           (\<lambda>i. p.f_eval ! i #
             get_authentication_path (length p.f_eval) i f_merkle)
           (p.powers_scaled idx)) @ rest
     \<rparr> \<le> t"
    by (rule list_out[OF _ outcome']) simp
	  show ?thesis
	    using result unfolding query_decommitment_transcript_def by simp
	qed

lemma check_decommit_on_query_step_preserves_query_counter:
  assumes step_in: "m \<in> set (v.check_decommit_on_query fr idx)"
    and outcome: "Some (x, t) \<in> set_dist (execute m s)"
  shows "PQueryCounter t = PQueryCounter s"
proof -
  from step_in obtain i where
    m_eq:
      "m = do {
        qh \<leftarrow> p.read;
        let len = scale * clength;
        qh_path \<leftarrow> ntimes p.read (floor_log len);
        ap \<leftarrow> p.check_authentication_path len i qh qh_path;
        assert (ap = fr);
        return qh
      }"
    unfolding v.check_decommit_on_query_def p.powers_scaled_def by auto
  from outcome[unfolded m_eq] obtain qh s1 qh_path s2 ap s3 s4 where
    read_qh: "Some (qh, s1) \<in> set_dist (execute p.read s)"
    and read_path:
      "Some (qh_path, s2) \<in>
        set_dist (execute (ntimes p.read (floor_log (scale * clength))) s1)"
    and check:
      "Some (ap, s3) \<in>
        set_dist (execute (p.check_authentication_path (scale * clength) i qh qh_path) s2)"
    and assert_ok: "Some ((), s4) \<in> set_dist (execute (assert (ap = fr)) s3)"
    and ret: "Some (x, t) \<in> set_dist (execute (return qh) s4)"
    by (auto simp: Let_def elim!: p.set_dist_bindE)
  have q_s1: "PQueryCounter s1 = PQueryCounter s"
    using read_preserves_counters[OF read_qh] by simp
  have q_s2: "PQueryCounter s2 = PQueryCounter s1"
    by (rule ntimes_read_preserves_query_counter[OF read_path])
  have q_s3: "PQueryCounter s3 = PQueryCounter s2"
    using p.check_authentication_path_preserves_channel(6)[OF check] .
  have s4_eq: "s4 = s3"
    using assert_outcomeD(2)[OF assert_ok] .
  have t_eq: "t = s4"
    using ret by simp
  show ?thesis
    using q_s1 q_s2 q_s3 unfolding s4_eq t_eq by simp
qed

lemma honest_root_alpha_degree_fri_final_query_from_prover_no_failure:
  assumes htv: "honest_trace_valid"
    and create_f:
      "Some (f_merkle, s1) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and send_f:
      "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
    and alphas:
      "Some (as, s3) \<in>
        set_dist (execute
          (mmap (replicate (length spec)
            (do {
              a \<leftarrow> p.receive_alpha_challenge;
              p.send a;
              return a
            }))) s2)"
    and cp'_def: "cp' = p.cp as p.f_powers"
    and send_degree:
      "Some ((), s4) \<in> set_dist (execute (p.send (of_nat (degree cp'))) s3)"
    and create_cp:
      "Some (cp_merkle, s5) \<in> set_dist (execute (p.create (p.cp_eval as)) s4)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.fri_commit nrounds [cp'] [p.eval_domain] [p.cp_eval as] [cp_merkle]) s5)"
    and final_send:
      "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    and random_idx:
      "Some (idx, s7) \<in> set_dist (execute p.receive_query_index_challenge s_final)"
    and idx_def: "idx' = p.index (to_nat idx)"
    and query_decommit:
      "Some (qouts, s8) \<in>
        set_dist (execute (mmap (p.decommit_on_query idx' f_merkle)) s7)"
    and fri_decommit:
      "Some (fri_idx, s9) \<in>
        set_dist (execute
          (mfold idx' (p.decommit_on_fri_layers (butlast (zip ls ms)))) s8)"
    and prover_state_eq: "prover_state = s9"
    and replay: "replay_state = verifier_replay_state prover_state"
  shows
    "None \<notin> dom (dist (execute
      (do {
        fr \<leftarrow> p.read;
        as' \<leftarrow> mmap (replicate (length spec)
          (do {
            a0 \<leftarrow> p.receive_alpha_challenge;
            let a0' = a0;
            a1 \<leftarrow> p.read;
            let a1' = a1;
            assert (a0' = a1');
            return a1'
          }));
        dg \<leftarrow> p.read;
        assert (to_nat dg \<le> p.maxDegree);
        fl \<leftarrow> ntimes v.receive_fri_commits nrounds;
        final \<leftarrow> p.read;
        idxv \<leftarrow> p.receive_query_index_challenge;
        let idxv' = p.index (to_nat idxv);
        fv \<leftarrow> mmap (v.check_decommit_on_query fr idxv');
        return (fr, as', dg, fl, final, idxv, fv)
      }) replay_state))"
proof -
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  let ?prefix_final =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      fl \<leftarrow> ntimes v.receive_fri_commits nrounds;
      final \<leftarrow> p.read;
      return (fr, as', dg, fl, final)
    }"
  let ?full =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      fl \<leftarrow> ntimes v.receive_fri_commits nrounds;
      final \<leftarrow> p.read;
      idxv \<leftarrow> p.receive_query_index_challenge;
      let idxv' = p.index (to_nat idxv);
      fv \<leftarrow> mmap (v.check_decommit_on_query fr idxv');
      return (fr, as', dg, fl, final, idxv, fv)
    }"
  have prefix_nf:
    "None \<notin> dom (dist (execute ?prefix_final replay_state))"
    by (rule honest_root_alpha_degree_fri_final_from_prover_no_failure[
        OF htv create_f send_f alphas cp'_def send_degree create_cp fri
          final_send random_idx idx_def query_decommit fri_decommit prover_state_eq replay])
  have root_alpha_tr:
    "length as = length spec \<and>
     PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
    by (rule prover_root_alpha_degree_transcript[
        OF create_f send_f alphas cp'_def send_degree])
  have later_hash: "s3 \<le> prover_state"
    by (rule prover_later_phases_hash_extends[
        OF send_degree create_cp fri final_send random_idx query_decommit fri_decommit prover_state_eq])
  have alpha_lookups:
    "\<forall>i < length as.
      fmlookup (HashMap replay_state)
        (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
        Some (as ! i)"
    by (rule prover_alpha_lookups_in_replay_state[
        OF create_f send_f alphas later_hash replay])
  from fri_commit_replay_data[OF fri] obtain roots challenges where
    len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and tr_s6: "PTranscript s6 = rev roots @ PTranscript s5"
    and st_s6: "PState s6 = foldl concat (PState s5) roots"
    and fri_hash: "s5 \<le> s6"
    and fri_lookups_s6:
      "\<forall>i < length roots.
        fmlookup (HashMap s6) (FiatShamirChallenge (foldl concat (PState s5) (take (Suc i) roots))) =
          Some (challenges ! i)"
    by blast
  from prover_query_decommitment_transcript_in_replay_state[
      OF final_send random_idx query_decommit fri_decommit prover_state_eq replay]
  obtain rest where replay_query_tr:
    "PTranscript replay_state =
      rev (PTranscript s6) @ [hd (last ls)] @
        query_decommitment_transcript idx' f_merkle @ rest"
    by blast
  have tr_s5: "PTranscript s5 = PTranscript s4"
    using create_preserves_transcript[OF create_cp] .
  have replay_prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
        roots @ [hd (last ls)] @ query_decommitment_transcript idx' f_merkle @ rest"
    using replay_query_tr tr_s6 tr_s5 root_alpha_tr cp'_def by simp
  have st_s1: "PState s1 = 0"
    using create_preserves_state[OF create_f]
    unfolding init_state_def by simp
  have send_f_res:
    "s2 = s1\<lparr>
      PState := concat (PState s1) (value f_merkle),
      PTranscript := value f_merkle # PTranscript s1\<rparr>"
    using p.send_outcome[OF send_f] .
  have alpha_data:
    "s2 \<le> s3 \<and> PState s3 = foldl concat (PState s2) as"
    using alpha_mmap_outcome[OF alphas] by simp
  have send_degree_res:
    "s4 = s3\<lparr>
      PState := concat (PState s3) (of_nat (degree cp')),
      PTranscript := of_nat (degree cp') # PTranscript s3\<rparr>"
    using p.send_outcome[OF send_degree] .
  have st_s5:
    "PState s5 =
      concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
        (of_nat (degree (p.cp as p.f_powers)))"
    using st_s1 send_f_res alpha_data send_degree_res
      create_preserves_state[OF create_cp] replay cp'_def
    unfolding verifier_replay_state_def by simp
  have after_hash: "s6 \<le> prover_state"
    by (rule prover_after_fri_hash_extends[
        OF final_send random_idx query_decommit fri_decommit prover_state_eq])
  have fri_lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap replay_state)
        (FiatShamirChallenge (foldl concat
          (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
            (of_nat (degree (p.cp as p.f_powers))))
          (take (Suc i) roots))) =
        Some (challenges ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length roots"
    have lookup_s6:
      "fmlookup (HashMap s6) (FiatShamirChallenge (foldl concat (PState s5) (take (Suc i) roots))) =
        Some (challenges ! i)"
      using fri_lookups_s6 i_bound by simp
    have lookup_prover:
      "fmlookup (HashMap prover_state) (FiatShamirChallenge (foldl concat (PState s5) (take (Suc i) roots))) =
        Some (challenges ! i)"
      using p.hash_extension_lookup[OF lookup_s6 after_hash] .
    show "fmlookup (HashMap replay_state)
      (FiatShamirChallenge (foldl concat
        (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
          (of_nat (degree (p.cp as p.f_powers))))
        (take (Suc i) roots))) =
      Some (challenges ! i)"
      using lookup_prover st_s5 replay
      unfolding verifier_replay_state_def by simp
  qed
  have final_send_res:
    "s_final = s6\<lparr>
      PState := concat (PState s6) (hd (last ls)),
      PTranscript := hd (last ls) # PTranscript s6\<rparr>"
    using p.send_outcome[OF final_send] .
  have query_lookup_replay:
    "fmlookup (HashMap replay_state) (QueryIndexChallenge (PQueryCounter s_final) (PState s_final)) = Some idx"
    by (rule prover_query_random_lookup_in_replay_state[
        OF random_idx query_decommit fri_decommit prover_state_eq replay])
  have s1_s2: "s1 \<le> s2"
    using p.send_outcome[OF send_f]
    unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s1_s3: "s1 \<le> s3"
    using s1_s2 alpha_data by (meson p.hash_ext_trans)
  have s3_prover: "s3 \<le> prover_state"
    using later_hash .
  have s1_prover: "s1 \<le> prover_state"
    using s1_s3 s3_prover by (meson p.hash_ext_trans)
  have s1_replay: "s1 \<le> replay_state"
    using s1_prover replay
    unfolding verifier_replay_state_def less_eq_hash_ext_def less_eq_fmap_def
    by simp
  have full_eq:
    "?full =
      (?prefix_final \<bind>
         (\<lambda>out. p.receive_query_index_challenge \<bind>
          (\<lambda>idxv.
            let idxv' = p.index (to_nat idxv) in
            mmap (v.check_decommit_on_query (case out of (fr, as', dg, fl, final) \<Rightarrow> fr) idxv') \<bind>
              (\<lambda>fv. return (case out of (fr, as', dg, fl, final) \<Rightarrow>
                (fr, as', dg, fl, final, idxv, fv))))))"
    by (simp add: sm_bind_assoc split: prod.splits)
  show ?thesis
    unfolding full_eq
  proof (rule no_failure_bindI[OF prefix_nf])
    fix out s_prefix
    assume prefix_out: "Some (out, s_prefix) \<in> set_dist (execute ?prefix_final replay_state)"
    obtain fr as' dg fl final where out_eq: "out = (fr, as', dg, fl, final)"
      by (cases out) auto
    have prefix_out':
      "Some ((fr, as', dg, fl, final), s_prefix) \<in>
        set_dist (execute ?prefix_final replay_state)"
      using prefix_out unfolding out_eq .
    have prefix_out_len:
      "Some ((fr, as', dg, fl, final), s_prefix) \<in> set_dist (execute
        (do {
          fr \<leftarrow> p.read;
          as' \<leftarrow> mmap (replicate (length spec) ?round);
          dg \<leftarrow> p.read;
          assert (to_nat dg \<le> p.maxDegree);
          fl \<leftarrow> ntimes v.receive_fri_commits (length roots);
          final \<leftarrow> p.read;
          return (fr, as', dg, fl, final)
        }) replay_state)"
      using prefix_out' len_roots by simp
    have prefix_res:
      "fr = value f_merkle \<and>
       as' = as \<and>
       dg = of_nat (degree (p.cp as p.f_powers)) \<and>
       fl = zip challenges roots \<and>
       final = hd (last ls) \<and>
       PState s_prefix =
         concat
           (foldl concat
             (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
               (of_nat (degree (p.cp as p.f_powers))))
             roots)
           (hd (last ls)) \<and>
       PTranscript s_prefix = query_decommitment_transcript idx' f_merkle @ rest \<and>
       replay_state \<le> s_prefix"
      by (rule honest_root_alpha_degree_fri_final_prefix_outcome[
          OF htv conjunct1[OF root_alpha_tr] _ replay_prefix alpha_lookups fri_lookups
            prefix_out_len])
        (use len_roots len_challenges in simp_all)
	    have st_prefix_final: "PState s_prefix = PState s_final"
	      using prefix_res st_s5 st_s6 final_send_res by simp
	    have q_prefix_replay: "PQueryCounter s_prefix = PQueryCounter replay_state"
	      by (rule honest_root_alpha_degree_fri_final_prefix_preserves_query_counter[
	          OF prefix_out_len])
	    have q_final_replay: "PQueryCounter s_final = PQueryCounter replay_state"
	      by (rule prover_final_query_counter_in_replay_state[
	          OF create_f send_f alphas send_degree create_cp fri final_send replay])
	    have lookup_prefix:
	      "fmlookup (HashMap s_prefix) (QueryIndexChallenge (PQueryCounter s_prefix) (PState s_prefix)) = Some idx"
	    proof -
	      have lookup:
	        "fmlookup (HashMap s_prefix) (QueryIndexChallenge (PQueryCounter s_final) (PState s_final)) = Some idx"
	        using p.hash_extension_lookup[OF query_lookup_replay, of s_prefix] prefix_res
	        by simp
	      then show ?thesis
	        using st_prefix_final q_prefix_replay q_final_replay by simp
	    qed
    show "None \<notin> dom (dist (execute
      (p.receive_query_index_challenge \<bind>
        (\<lambda>idxv.
          let idxv' = p.index (to_nat idxv)
          in mmap
              (v.check_decommit_on_query
                (case out of (fr, as', dg, fl, final) \<Rightarrow> fr) idxv') \<bind>
             (\<lambda>fv.
               return
                (case out of (fr, as', dg, fl, final) \<Rightarrow>
                  (fr, as', dg, fl, final, idxv, fv))))) s_prefix))"
    proof (rule no_failure_bindI)
      show "None \<notin> dom (dist (execute p.receive_query_index_challenge s_prefix))"
        by (rule p.receive_query_index_challenge_no_failure)
    next
      fix idxv s_idx
      assume rand_v:
        "Some (idxv, s_idx) \<in> set_dist (execute p.receive_query_index_challenge s_prefix)"
      have rand_res:
        "idxv = idx \<and>
         PState s_idx = PState s_prefix \<and>
         PTranscript s_idx = PTranscript s_prefix \<and>
         s_prefix \<le> s_idx"
        using p.receive_query_index_challenge_known_outcome[OF lookup_prefix rand_v]
        by simp
      have s1_s_idx: "s1 \<le> s_idx"
        using s1_replay prefix_res rand_res by (meson p.hash_ext_trans)
      have tr_idx:
        "PTranscript s_idx =
          query_decommitment_transcript (p.index (to_nat idxv)) f_merkle @ rest"
        using rand_res prefix_res idx_def by simp
      have query_nf:
        "None \<notin> dom (dist (execute
          (mmap (v.check_decommit_on_query fr (p.index (to_nat idxv)))) s_idx))"
        by (rule honest_query_decommitment_replay_no_failure[
            OF create_f s1_s_idx _ tr_idx])
          (use prefix_res in simp)
      show "None \<notin> dom (dist (execute
        ((let idxv' = p.index (to_nat idxv)
          in mmap
              (v.check_decommit_on_query
                (case out of (fr, as', dg, fl, final) \<Rightarrow> fr) idxv') \<bind>
             (\<lambda>fv.
               return
                (case out of (fr, as', dg, fl, final) \<Rightarrow>
                  (fr, as', dg, fl, final, idxv, fv))))) s_idx))"
        unfolding out_eq
        by (simp add: no_failure_bind_returnI[OF query_nf])
    qed
  qed
qed

lemma honest_root_alpha_degree_fri_final_query_dynamic_from_prover_no_failure:
  assumes htv: "honest_trace_valid"
    and create_f:
      "Some (f_merkle, s1) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and send_f:
      "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
    and alphas:
      "Some (as, s3) \<in>
        set_dist (execute
          (mmap (replicate (length spec)
            (do {
              a \<leftarrow> p.receive_alpha_challenge;
              p.send a;
              return a
            }))) s2)"
    and cp'_def: "cp' = p.cp as p.f_powers"
    and send_degree:
      "Some ((), s4) \<in> set_dist (execute (p.send (of_nat (degree cp'))) s3)"
    and create_cp:
      "Some (cp_merkle, s5) \<in> set_dist (execute (p.create (p.cp_eval as)) s4)"
    and nrounds_def: "nrounds = ceil_log (degree cp' + 1)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.fri_commit nrounds [cp'] [p.eval_domain] [p.cp_eval as] [cp_merkle]) s5)"
    and final_send:
      "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    and random_idx:
      "Some (idx, s7) \<in> set_dist (execute p.receive_query_index_challenge s_final)"
    and idx_def: "idx' = p.index (to_nat idx)"
    and query_decommit:
      "Some (qouts, s8) \<in>
        set_dist (execute (mmap (p.decommit_on_query idx' f_merkle)) s7)"
    and fri_decommit:
      "Some (fri_idx, s9) \<in>
        set_dist (execute
          (mfold idx' (p.decommit_on_fri_layers (butlast (zip ls ms)))) s8)"
    and prover_state_eq: "prover_state = s9"
    and replay: "replay_state = verifier_replay_state prover_state"
  shows
    "None \<notin> dom (dist (execute
      (do {
        fr \<leftarrow> p.read;
        as' \<leftarrow> mmap (replicate (length spec)
          (do {
            a0 \<leftarrow> p.receive_alpha_challenge;
            let a0' = a0;
            a1 \<leftarrow> p.read;
            let a1' = a1;
            assert (a0' = a1');
            return a1'
          }));
        dg \<leftarrow> p.read;
        assert (to_nat dg \<le> p.maxDegree);
        fl \<leftarrow> ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1));
        final \<leftarrow> p.read;
        idxv \<leftarrow> p.receive_query_index_challenge;
        let idxv' = p.index (to_nat idxv);
        fv \<leftarrow> mmap (v.check_decommit_on_query fr idxv');
        return (fr, as', dg, fl, final, idxv, fv)
      }) replay_state))"
proof -
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  let ?prefix_final =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      fl \<leftarrow> ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1));
      final \<leftarrow> p.read;
      return (fr, as', dg, fl, final)
    }"
  let ?full =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      fl \<leftarrow> ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1));
      final \<leftarrow> p.read;
      idxv \<leftarrow> p.receive_query_index_challenge;
      let idxv' = p.index (to_nat idxv);
      fv \<leftarrow> mmap (v.check_decommit_on_query fr idxv');
      return (fr, as', dg, fl, final, idxv, fv)
    }"
  have prefix_nf:
    "None \<notin> dom (dist (execute ?prefix_final replay_state))"
    by (rule honest_root_alpha_degree_fri_final_dynamic_from_prover_no_failure[
        OF htv create_f send_f alphas cp'_def send_degree create_cp nrounds_def fri
          final_send random_idx idx_def query_decommit fri_decommit prover_state_eq replay])
  have root_alpha_tr:
    "length as = length spec \<and>
     PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
    by (rule prover_root_alpha_degree_transcript[
        OF create_f send_f alphas cp'_def send_degree])
  have later_hash: "s3 \<le> prover_state"
    by (rule prover_later_phases_hash_extends[
        OF send_degree create_cp fri final_send random_idx query_decommit fri_decommit prover_state_eq])
  have alpha_lookups:
    "\<forall>i < length as.
      fmlookup (HashMap replay_state)
        (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
        Some (as ! i)"
    by (rule prover_alpha_lookups_in_replay_state[
        OF create_f send_f alphas later_hash replay])
  from fri_commit_replay_data[OF fri] obtain roots challenges where
    len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and tr_s6: "PTranscript s6 = rev roots @ PTranscript s5"
    and st_s6: "PState s6 = foldl concat (PState s5) roots"
    and fri_hash: "s5 \<le> s6"
    and fri_lookups_s6:
      "\<forall>i < length roots.
        fmlookup (HashMap s6) (FiatShamirChallenge (foldl concat (PState s5) (take (Suc i) roots))) =
          Some (challenges ! i)"
    by blast
  from prover_query_decommitment_transcript_in_replay_state[
      OF final_send random_idx query_decommit fri_decommit prover_state_eq replay]
  obtain rest where replay_query_tr:
    "PTranscript replay_state =
      rev (PTranscript s6) @ [hd (last ls)] @
        query_decommitment_transcript idx' f_merkle @ rest"
    by blast
  have tr_s5: "PTranscript s5 = PTranscript s4"
    using create_preserves_transcript[OF create_cp] .
  have replay_prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
        roots @ [hd (last ls)] @ query_decommitment_transcript idx' f_merkle @ rest"
    using replay_query_tr tr_s6 tr_s5 root_alpha_tr cp'_def by simp
  have st_s1: "PState s1 = 0"
    using create_preserves_state[OF create_f]
    unfolding init_state_def by simp
  have send_f_res:
    "s2 = s1\<lparr>
      PState := concat (PState s1) (value f_merkle),
      PTranscript := value f_merkle # PTranscript s1\<rparr>"
    using p.send_outcome[OF send_f] .
  have alpha_data:
    "s2 \<le> s3 \<and> PState s3 = foldl concat (PState s2) as"
    using alpha_mmap_outcome[OF alphas] by simp
  have send_degree_res:
    "s4 = s3\<lparr>
      PState := concat (PState s3) (of_nat (degree cp')),
      PTranscript := of_nat (degree cp') # PTranscript s3\<rparr>"
    using p.send_outcome[OF send_degree] .
  have st_s5:
    "PState s5 =
      concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
        (of_nat (degree (p.cp as p.f_powers)))"
    using st_s1 send_f_res alpha_data send_degree_res
      create_preserves_state[OF create_cp] replay cp'_def
    unfolding verifier_replay_state_def by simp
  have after_hash: "s6 \<le> prover_state"
    by (rule prover_after_fri_hash_extends[
        OF final_send random_idx query_decommit fri_decommit prover_state_eq])
  have fri_lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap replay_state)
        (FiatShamirChallenge (foldl concat
          (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
            (of_nat (degree (p.cp as p.f_powers))))
          (take (Suc i) roots))) =
        Some (challenges ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length roots"
    have lookup_s6:
      "fmlookup (HashMap s6) (FiatShamirChallenge (foldl concat (PState s5) (take (Suc i) roots))) =
        Some (challenges ! i)"
      using fri_lookups_s6 i_bound by simp
    have lookup_prover:
      "fmlookup (HashMap prover_state) (FiatShamirChallenge (foldl concat (PState s5) (take (Suc i) roots))) =
        Some (challenges ! i)"
      using p.hash_extension_lookup[OF lookup_s6 after_hash] .
    show "fmlookup (HashMap replay_state)
      (FiatShamirChallenge (foldl concat
        (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
          (of_nat (degree (p.cp as p.f_powers))))
        (take (Suc i) roots))) =
      Some (challenges ! i)"
      using lookup_prover st_s5 replay
      unfolding verifier_replay_state_def by simp
  qed
  have final_send_res:
    "s_final = s6\<lparr>
      PState := concat (PState s6) (hd (last ls)),
      PTranscript := hd (last ls) # PTranscript s6\<rparr>"
    using p.send_outcome[OF final_send] .
  have query_lookup_replay:
    "fmlookup (HashMap replay_state) (QueryIndexChallenge (PQueryCounter s_final) (PState s_final)) = Some idx"
    by (rule prover_query_random_lookup_in_replay_state[
        OF random_idx query_decommit fri_decommit prover_state_eq replay])
  have s1_s2: "s1 \<le> s2"
    using p.send_outcome[OF send_f]
    unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s1_s3: "s1 \<le> s3"
    using s1_s2 alpha_data by (meson p.hash_ext_trans)
  have s3_prover: "s3 \<le> prover_state"
    using later_hash .
  have s1_prover: "s1 \<le> prover_state"
    using s1_s3 s3_prover by (meson p.hash_ext_trans)
  have s1_replay: "s1 \<le> replay_state"
    using s1_prover replay
    unfolding verifier_replay_state_def less_eq_hash_ext_def less_eq_fmap_def
    by simp
  have roots_rounds:
    "length roots = ceil_log (degree (p.cp as p.f_powers) + 1)"
    using len_roots nrounds_def cp'_def by simp
  have full_eq:
    "?full =
      (?prefix_final \<bind>
         (\<lambda>out. p.receive_query_index_challenge \<bind>
          (\<lambda>idxv.
            let idxv' = p.index (to_nat idxv) in
            mmap (v.check_decommit_on_query (case out of (fr, as', dg, fl, final) \<Rightarrow> fr) idxv') \<bind>
              (\<lambda>fv. return (case out of (fr, as', dg, fl, final) \<Rightarrow>
                (fr, as', dg, fl, final, idxv, fv))))))"
    by (simp add: sm_bind_assoc split: prod.splits)
  show ?thesis
    unfolding full_eq
  proof (rule no_failure_bindI[OF prefix_nf])
    fix out s_prefix
    assume prefix_out: "Some (out, s_prefix) \<in> set_dist (execute ?prefix_final replay_state)"
    obtain fr as' dg fl final where out_eq: "out = (fr, as', dg, fl, final)"
      by (cases out) auto
    have prefix_out':
      "Some ((fr, as', dg, fl, final), s_prefix) \<in>
        set_dist (execute ?prefix_final replay_state)"
      using prefix_out unfolding out_eq .
    have prefix_res:
      "fr = value f_merkle \<and>
       as' = as \<and>
       dg = of_nat (degree (p.cp as p.f_powers)) \<and>
       fl = zip challenges roots \<and>
       final = hd (last ls) \<and>
       PState s_prefix =
         concat
           (foldl concat
             (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
               (of_nat (degree (p.cp as p.f_powers))))
             roots)
           (hd (last ls)) \<and>
       PTranscript s_prefix = query_decommitment_transcript idx' f_merkle @ rest \<and>
       replay_state \<le> s_prefix"
      by (rule honest_root_alpha_degree_fri_final_dynamic_prefix_outcome[
          OF htv conjunct1[OF root_alpha_tr] _ roots_rounds replay_prefix
            alpha_lookups fri_lookups prefix_out'])
        (use len_roots len_challenges in simp_all)
	    have st_prefix_final: "PState s_prefix = PState s_final"
	      using prefix_res st_s5 st_s6 final_send_res by simp
	    have q_prefix_replay: "PQueryCounter s_prefix = PQueryCounter replay_state"
	      by (rule honest_root_alpha_degree_fri_final_dynamic_prefix_preserves_query_counter[
	          OF prefix_out'])
	    have q_final_replay: "PQueryCounter s_final = PQueryCounter replay_state"
	      by (rule prover_final_query_counter_in_replay_state[
	          OF create_f send_f alphas send_degree create_cp fri final_send replay])
	  have lookup_prefix:
	      "fmlookup (HashMap s_prefix) (QueryIndexChallenge (PQueryCounter s_prefix) (PState s_prefix)) = Some idx"
	    proof -
	      have lookup:
	        "fmlookup (HashMap s_prefix) (QueryIndexChallenge (PQueryCounter s_final) (PState s_final)) = Some idx"
	        using p.hash_extension_lookup[OF query_lookup_replay, of s_prefix] prefix_res
	        by simp
	      then show ?thesis
	        using st_prefix_final q_prefix_replay q_final_replay by simp
	    qed
    show "None \<notin> dom (dist (execute
      (p.receive_query_index_challenge \<bind>
        (\<lambda>idxv.
          let idxv' = p.index (to_nat idxv)
          in mmap
              (v.check_decommit_on_query
                (case out of (fr, as', dg, fl, final) \<Rightarrow> fr) idxv') \<bind>
             (\<lambda>fv.
               return
                (case out of (fr, as', dg, fl, final) \<Rightarrow>
                  (fr, as', dg, fl, final, idxv, fv))))) s_prefix))"
    proof (rule no_failure_bindI)
      show "None \<notin> dom (dist (execute p.receive_query_index_challenge s_prefix))"
        by (rule p.receive_query_index_challenge_no_failure)
    next
      fix idxv s_idx
      assume rand_v:
        "Some (idxv, s_idx) \<in> set_dist (execute p.receive_query_index_challenge s_prefix)"
      have rand_res:
        "idxv = idx \<and>
         PState s_idx = PState s_prefix \<and>
         PTranscript s_idx = PTranscript s_prefix \<and>
         s_prefix \<le> s_idx"
        using p.receive_query_index_challenge_known_outcome[OF lookup_prefix rand_v]
        by simp
      have s1_s_idx: "s1 \<le> s_idx"
        using s1_replay prefix_res rand_res by (meson p.hash_ext_trans)
      have tr_idx:
        "PTranscript s_idx =
          query_decommitment_transcript (p.index (to_nat idxv)) f_merkle @ rest"
        using rand_res prefix_res idx_def by simp
      have query_nf:
        "None \<notin> dom (dist (execute
          (mmap (v.check_decommit_on_query fr (p.index (to_nat idxv)))) s_idx))"
        by (rule honest_query_decommitment_replay_no_failure[
            OF create_f s1_s_idx _ tr_idx])
          (use prefix_res in simp)
      show "None \<notin> dom (dist (execute
        ((let idxv' = p.index (to_nat idxv)
          in mmap
              (v.check_decommit_on_query
                (case out of (fr, as', dg, fl, final) \<Rightarrow> fr) idxv') \<bind>
             (\<lambda>fv.
               return
                (case out of (fr, as', dg, fl, final) \<Rightarrow>
                  (fr, as', dg, fl, final, idxv, fv))))) s_idx))"
        unfolding out_eq
        by (simp add: no_failure_bind_returnI[OF query_nf])
    qed
  qed
qed

lemma honest_root_alpha_degree_fri_final_query_dynamic_outcome_to_fixed:
  assumes htv: "honest_trace_valid"
    and create_f:
      "Some (f_merkle, s1) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and send_f:
      "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
    and alphas:
      "Some (as, s3) \<in>
        set_dist (execute
          (mmap (replicate (length spec)
            (do {
              a \<leftarrow> p.receive_alpha_challenge;
              p.send a;
              return a
            }))) s2)"
    and cp'_def: "cp' = p.cp as p.f_powers"
    and send_degree:
      "Some ((), s4) \<in> set_dist (execute (p.send (of_nat (degree cp'))) s3)"
    and create_cp:
      "Some (cp_merkle, s5) \<in> set_dist (execute (p.create (p.cp_eval as)) s4)"
    and nrounds_def: "nrounds = ceil_log (degree cp' + 1)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.fri_commit nrounds [cp'] [p.eval_domain] [p.cp_eval as] [cp_merkle]) s5)"
    and final_send:
      "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    and random_idx:
      "Some (idx, s7) \<in> set_dist (execute p.receive_query_index_challenge s_final)"
    and idx_def: "idx' = p.index (to_nat idx)"
    and query_decommit:
      "Some (qouts, s8) \<in>
        set_dist (execute (mmap (p.decommit_on_query idx' f_merkle)) s7)"
    and fri_decommit:
      "Some (fri_idx, s9) \<in>
        set_dist (execute
          (mfold idx' (p.decommit_on_fri_layers (butlast (zip ls ms)))) s8)"
    and prover_state_eq: "prover_state = s9"
    and replay: "replay_state = verifier_replay_state prover_state"
    and outcome:
      "Some ((fr, as', dg, fl, final, idxv, fv), t) \<in>
        set_dist (execute
          (do {
            fr \<leftarrow> p.read;
            as' \<leftarrow> mmap (replicate (length spec)
              (do {
                a0 \<leftarrow> p.receive_alpha_challenge;
                let a0' = a0;
                a1 \<leftarrow> p.read;
                let a1' = a1;
                assert (a0' = a1');
                return a1'
              }));
            dg \<leftarrow> p.read;
            assert (to_nat dg \<le> p.maxDegree);
            fl \<leftarrow> ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1));
            final \<leftarrow> p.read;
            idxv \<leftarrow> p.receive_query_index_challenge;
            let idxv' = p.index (to_nat idxv);
            fv \<leftarrow> mmap (v.check_decommit_on_query fr idxv');
            return (fr, as', dg, fl, final, idxv, fv)
          }) replay_state)"
  shows
      "Some ((fr, as', dg, fl, final, idxv, fv), t) \<in>
        set_dist (execute
          (do {
            fr \<leftarrow> p.read;
            as' \<leftarrow> mmap (replicate (length spec)
              (do {
                a0 \<leftarrow> p.receive_alpha_challenge;
                let a0' = a0;
                a1 \<leftarrow> p.read;
                let a1' = a1;
                assert (a0' = a1');
                return a1'
              }));
            dg \<leftarrow> p.read;
            assert (to_nat dg \<le> p.maxDegree);
            fl \<leftarrow> ntimes v.receive_fri_commits nrounds;
            final \<leftarrow> p.read;
            idxv \<leftarrow> p.receive_query_index_challenge;
            let idxv' = p.index (to_nat idxv);
            fv \<leftarrow> mmap (v.check_decommit_on_query fr idxv');
            return (fr, as', dg, fl, final, idxv, fv)
          }) replay_state)"
proof -
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  from outcome obtain r1 r2 r3 r4 r5 r6 r7 where
    read_fr: "Some (fr, r1) \<in> set_dist (execute p.read replay_state)"
    and alpha_out:
      "Some (as', r2) \<in>
        set_dist (execute (mmap (replicate (length spec) ?round)) r1)"
    and read_dg: "Some (dg, r3) \<in> set_dist (execute p.read r2)"
    and degree_assert:
      "Some ((), r4) \<in> set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) r3)"
    and fri_reads:
      "Some (fl, r5) \<in>
        set_dist (execute (ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1))) r4)"
    and read_final: "Some (final, r6) \<in> set_dist (execute p.read r5)"
    and random_v:
      "Some (idxv, r7) \<in> set_dist (execute p.receive_query_index_challenge r6)"
    and query_reads:
      "Some (fv, t) \<in>
        set_dist (execute (mmap (v.check_decommit_on_query fr (p.index (to_nat idxv)))) r7)"
    by (auto simp: Let_def elim!: p.set_dist_bindE)
  let ?rad =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      return (fr, as', dg)
    }"
  have rad_out:
    "Some ((fr, as', dg), r4) \<in> set_dist (execute ?rad replay_state)"
    apply (rule set_dist_bindI[OF read_fr])
    apply (rule set_dist_bindI[OF alpha_out])
    apply (rule set_dist_bindI[OF read_dg])
    apply (rule set_dist_bindI[OF degree_assert])
    by simp
  have dg_eq: "dg = of_nat (degree (p.cp as p.f_powers))"
    using honest_root_alpha_degree_from_prover_outcome[
      OF htv create_f send_f alphas cp'_def send_degree create_cp fri
        final_send random_idx idx_def query_decommit fri_decommit prover_state_eq
        replay rad_out]
    by blast
  have rounds_eq: "ceil_log (to_nat dg + 1) = nrounds"
    using honest_degree_message_rounds[OF htv, of as] dg_eq cp'_def nrounds_def
    by simp
  have fri_reads_fixed:
    "Some (fl, r5) \<in> set_dist (execute (ntimes v.receive_fri_commits nrounds) r4)"
    using fri_reads rounds_eq by simp
  show ?thesis
    apply (rule set_dist_bindI[OF read_fr])
    apply (rule set_dist_bindI[OF alpha_out])
    apply (rule set_dist_bindI[OF read_dg])
    apply (rule set_dist_bindI[OF degree_assert])
    apply (rule set_dist_bindI[OF fri_reads_fixed])
    apply (rule set_dist_bindI[OF read_final])
    apply (rule set_dist_bindI[OF random_v])
    apply (simp add: Let_def)
    apply (rule set_dist_bindI[OF query_reads])
    by simp
qed

lemma honest_root_alpha_degree_fri_final_query_from_prover_outcome:
  assumes htv: "honest_trace_valid"
    and create_f:
      "Some (f_merkle, s1) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and send_f:
      "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
    and alphas:
      "Some (as, s3) \<in>
        set_dist (execute
          (mmap (replicate (length spec)
            (do {
              a \<leftarrow> p.receive_alpha_challenge;
              p.send a;
              return a
            }))) s2)"
    and cp'_def: "cp' = p.cp as p.f_powers"
    and send_degree:
      "Some ((), s4) \<in> set_dist (execute (p.send (of_nat (degree cp'))) s3)"
    and create_cp:
      "Some (cp_merkle, s5) \<in> set_dist (execute (p.create (p.cp_eval as)) s4)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.fri_commit nrounds [cp'] [p.eval_domain] [p.cp_eval as] [cp_merkle]) s5)"
    and final_send:
      "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    and random_idx:
      "Some (idx, s7) \<in> set_dist (execute p.receive_query_index_challenge s_final)"
    and idx_def: "idx' = p.index (to_nat idx)"
    and query_decommit:
      "Some (qouts, s8) \<in>
        set_dist (execute (mmap (p.decommit_on_query idx' f_merkle)) s7)"
    and fri_decommit:
      "Some (fri_idx, s9) \<in>
        set_dist (execute
          (mfold idx' (p.decommit_on_fri_layers (butlast (zip ls ms)))) s8)"
    and prover_state_eq: "prover_state = s9"
    and replay: "replay_state = verifier_replay_state prover_state"
    and outcome:
      "Some ((fr, as', dg, fl, final, idxv, fv), t) \<in>
        set_dist (execute
          (do {
            fr \<leftarrow> p.read;
            as' \<leftarrow> mmap (replicate (length spec)
              (do {
                a0 \<leftarrow> p.receive_alpha_challenge;
                let a0' = a0;
                a1 \<leftarrow> p.read;
                let a1' = a1;
                assert (a0' = a1');
                return a1'
              }));
            dg \<leftarrow> p.read;
            assert (to_nat dg \<le> p.maxDegree);
            fl \<leftarrow> ntimes v.receive_fri_commits nrounds;
            final \<leftarrow> p.read;
            idxv \<leftarrow> p.receive_query_index_challenge;
            let idxv' = p.index (to_nat idxv);
            fv \<leftarrow> mmap (v.check_decommit_on_query fr idxv');
            return (fr, as', dg, fl, final, idxv, fv)
          }) replay_state)"
  shows
    "fr = value f_merkle \<and>
     as' = as \<and>
     dg = of_nat (degree (p.cp as p.f_powers)) \<and>
     final = hd (last ls) \<and>
     idxv = idx \<and>
     fv = map (\<lambda>i. p.f_eval ! i) (p.powers_scaled idx') \<and>
     replay_state \<le> t \<and>
     (\<exists>roots challenges rest.
       length roots = nrounds \<and>
       length challenges = nrounds \<and>
       fl = zip challenges roots \<and>
       (\<forall>j < nrounds. roots ! j = value (ms ! j)) \<and>
       (\<forall>j < nrounds.
          p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
            (ps ! Suc j, ds ! Suc j, ls ! Suc j)) \<and>
       PTranscript t = rest \<and>
       PTranscript replay_state =
         value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
           roots @ [hd (last ls)] @
           query_decommitment_transcript idx' f_merkle @ rest)"
proof -
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  let ?prefix_final =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      fl \<leftarrow> ntimes v.receive_fri_commits nrounds;
      final \<leftarrow> p.read;
      return (fr, as', dg, fl, final)
    }"
  let ?full =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      fl \<leftarrow> ntimes v.receive_fri_commits nrounds;
      final \<leftarrow> p.read;
      idxv \<leftarrow> p.receive_query_index_challenge;
      let idxv' = p.index (to_nat idxv);
      fv \<leftarrow> mmap (v.check_decommit_on_query fr idxv');
      return (fr, as', dg, fl, final, idxv, fv)
    }"
  have root_alpha_tr:
    "length as = length spec \<and>
     PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
    by (rule prover_root_alpha_degree_transcript[
        OF create_f send_f alphas cp'_def send_degree])
  have later_hash: "s3 \<le> prover_state"
    by (rule prover_later_phases_hash_extends[
        OF send_degree create_cp fri final_send random_idx query_decommit fri_decommit prover_state_eq])
  have alpha_lookups:
    "\<forall>i < length as.
      fmlookup (HashMap replay_state)
        (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
        Some (as ! i)"
    by (rule prover_alpha_lookups_in_replay_state[
        OF create_f send_f alphas later_hash replay])
  from fri_commit_initial_replay_successor_data[OF fri] obtain roots challenges where
    len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and tr_s6: "PTranscript s6 = rev roots @ PTranscript s5"
    and st_s6: "PState s6 = foldl concat (PState s5) roots"
    and fri_hash: "s5 \<le> s6"
    and fri_lookups_s6:
      "\<forall>i < length roots.
        fmlookup (HashMap s6) (FiatShamirChallenge (foldl concat (PState s5) (take (Suc i) roots))) =
          Some (challenges ! i)"
    and roots_aligned: "\<forall>j < nrounds. roots ! j = value (ms ! j)"
    and successors:
      "\<forall>j < nrounds.
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    by blast
  from prover_query_decommitment_transcript_in_replay_state[
      OF final_send random_idx query_decommit fri_decommit prover_state_eq replay]
  obtain rest where replay_query_tr:
    "PTranscript replay_state =
      rev (PTranscript s6) @ [hd (last ls)] @
        query_decommitment_transcript idx' f_merkle @ rest"
    by blast
  have tr_s5: "PTranscript s5 = PTranscript s4"
    using create_preserves_transcript[OF create_cp] .
  have replay_prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
        roots @ [hd (last ls)] @ query_decommitment_transcript idx' f_merkle @ rest"
    using replay_query_tr tr_s6 tr_s5 root_alpha_tr cp'_def by simp
  have st_s1: "PState s1 = 0"
    using create_preserves_state[OF create_f]
    unfolding init_state_def by simp
  have send_f_res:
    "s2 = s1\<lparr>
      PState := concat (PState s1) (value f_merkle),
      PTranscript := value f_merkle # PTranscript s1\<rparr>"
    using p.send_outcome[OF send_f] .
  have alpha_data:
    "s2 \<le> s3 \<and> PState s3 = foldl concat (PState s2) as"
    using alpha_mmap_outcome[OF alphas] by simp
  have send_degree_res:
    "s4 = s3\<lparr>
      PState := concat (PState s3) (of_nat (degree cp')),
      PTranscript := of_nat (degree cp') # PTranscript s3\<rparr>"
    using p.send_outcome[OF send_degree] .
  have st_s5:
    "PState s5 =
      concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
        (of_nat (degree (p.cp as p.f_powers)))"
    using st_s1 send_f_res alpha_data send_degree_res
      create_preserves_state[OF create_cp] replay cp'_def
    unfolding verifier_replay_state_def by simp
  have after_hash: "s6 \<le> prover_state"
    by (rule prover_after_fri_hash_extends[
        OF final_send random_idx query_decommit fri_decommit prover_state_eq])
  have fri_lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap replay_state)
        (FiatShamirChallenge (foldl concat
          (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
            (of_nat (degree (p.cp as p.f_powers))))
          (take (Suc i) roots))) =
        Some (challenges ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length roots"
    have lookup_s6:
      "fmlookup (HashMap s6) (FiatShamirChallenge (foldl concat (PState s5) (take (Suc i) roots))) =
        Some (challenges ! i)"
      using fri_lookups_s6 i_bound by simp
    have lookup_prover:
      "fmlookup (HashMap prover_state) (FiatShamirChallenge (foldl concat (PState s5) (take (Suc i) roots))) =
        Some (challenges ! i)"
      using p.hash_extension_lookup[OF lookup_s6 after_hash] .
    show "fmlookup (HashMap replay_state)
      (FiatShamirChallenge (foldl concat
        (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
          (of_nat (degree (p.cp as p.f_powers))))
        (take (Suc i) roots))) =
      Some (challenges ! i)"
      using lookup_prover st_s5 replay
      unfolding verifier_replay_state_def by simp
  qed
  have final_send_res:
    "s_final = s6\<lparr>
      PState := concat (PState s6) (hd (last ls)),
      PTranscript := hd (last ls) # PTranscript s6\<rparr>"
    using p.send_outcome[OF final_send] .
  have query_lookup_replay:
    "fmlookup (HashMap replay_state) (QueryIndexChallenge (PQueryCounter s_final) (PState s_final)) = Some idx"
    by (rule prover_query_random_lookup_in_replay_state[
        OF random_idx query_decommit fri_decommit prover_state_eq replay])
  have s1_s2: "s1 \<le> s2"
    using p.send_outcome[OF send_f]
    unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s1_s3: "s1 \<le> s3"
    using s1_s2 alpha_data by (meson p.hash_ext_trans)
  have s3_prover: "s3 \<le> prover_state"
    using later_hash .
  have s1_prover: "s1 \<le> prover_state"
    using s1_s3 s3_prover by (meson p.hash_ext_trans)
  have s1_replay: "s1 \<le> replay_state"
    using s1_prover replay
    unfolding verifier_replay_state_def less_eq_hash_ext_def less_eq_fmap_def
    by simp
  have full_eq:
    "?full =
      (?prefix_final \<bind>
         (\<lambda>out. p.receive_query_index_challenge \<bind>
          (\<lambda>idxv.
            let idxv' = p.index (to_nat idxv) in
            mmap (v.check_decommit_on_query (case out of (fr, as', dg, fl, final) \<Rightarrow> fr) idxv') \<bind>
              (\<lambda>fv. return (case out of (fr, as', dg, fl, final) \<Rightarrow>
                (fr, as', dg, fl, final, idxv, fv))))))"
    by (simp add: sm_bind_assoc split: prod.splits)
  have outcome_full:
    "Some ((fr, as', dg, fl, final, idxv, fv), t) \<in>
      set_dist (execute ?full replay_state)"
    using outcome by simp
  from outcome_full[unfolded full_eq] obtain out s_prefix where
    prefix_out: "Some (out, s_prefix) \<in> set_dist (execute ?prefix_final replay_state)"
    and after_prefix:
      "Some ((fr, as', dg, fl, final, idxv, fv), t) \<in>
        set_dist (execute
          (p.receive_query_index_challenge \<bind>
            (\<lambda>idxv.
              let idxv' = p.index (to_nat idxv) in
              mmap (v.check_decommit_on_query
                (case out of (fr, as', dg, fl, final) \<Rightarrow> fr) idxv') \<bind>
                (\<lambda>fv. return (case out of (fr, as', dg, fl, final) \<Rightarrow>
                  (fr, as', dg, fl, final, idxv, fv))))) s_prefix)"
  proof -
    show ?thesis
      using outcome_full[unfolded full_eq]
    proof (rule p.set_dist_bindE)
      fix out s_prefix
      assume prefix_out:
        "Some (out, s_prefix) \<in> set_dist (execute ?prefix_final replay_state)"
        and after_prefix:
          "Some ((fr, as', dg, fl, final, idxv, fv), t) \<in>
            set_dist (execute
              (p.receive_query_index_challenge \<bind>
                (\<lambda>idxv.
                  let idxv' = p.index (to_nat idxv) in
                  mmap (v.check_decommit_on_query
                    (case out of (fr, as', dg, fl, final) \<Rightarrow> fr) idxv') \<bind>
                    (\<lambda>fv. return (case out of (fr, as', dg, fl, final) \<Rightarrow>
                      (fr, as', dg, fl, final, idxv, fv))))) s_prefix)"
      show ?thesis
        by (rule that[OF prefix_out after_prefix])
    qed
  qed
  obtain fr0 as0 dg0 fl0 final0 where out_eq:
    "out = (fr0, as0, dg0, fl0, final0)"
    by (cases out) auto
  have prefix_out':
    "Some ((fr0, as0, dg0, fl0, final0), s_prefix) \<in>
      set_dist (execute ?prefix_final replay_state)"
    using prefix_out unfolding out_eq .
  have prefix_out_len:
    "Some ((fr0, as0, dg0, fl0, final0), s_prefix) \<in> set_dist (execute
      (do {
        fr \<leftarrow> p.read;
        as' \<leftarrow> mmap (replicate (length spec) ?round);
        dg \<leftarrow> p.read;
        assert (to_nat dg \<le> p.maxDegree);
        fl \<leftarrow> ntimes v.receive_fri_commits (length roots);
        final \<leftarrow> p.read;
        return (fr, as', dg, fl, final)
      }) replay_state)"
    using prefix_out' len_roots by simp
  have prefix_res:
    "fr0 = value f_merkle \<and>
     as0 = as \<and>
     dg0 = of_nat (degree (p.cp as p.f_powers)) \<and>
     fl0 = zip challenges roots \<and>
     final0 = hd (last ls) \<and>
     PState s_prefix =
       concat
         (foldl concat
           (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
             (of_nat (degree (p.cp as p.f_powers))))
           roots)
         (hd (last ls)) \<and>
     PTranscript s_prefix = query_decommitment_transcript idx' f_merkle @ rest \<and>
     replay_state \<le> s_prefix"
    by (rule honest_root_alpha_degree_fri_final_prefix_outcome[
        OF htv conjunct1[OF root_alpha_tr] _ replay_prefix alpha_lookups fri_lookups
          prefix_out_len])
      (use len_roots len_challenges in simp_all)
	  have st_prefix_final: "PState s_prefix = PState s_final"
	    using prefix_res st_s5 st_s6 final_send_res by simp
	  have q_prefix_replay: "PQueryCounter s_prefix = PQueryCounter replay_state"
	    by (rule honest_root_alpha_degree_fri_final_prefix_preserves_query_counter[
	        OF prefix_out_len])
	  have q_final_replay: "PQueryCounter s_final = PQueryCounter replay_state"
	    by (rule prover_final_query_counter_in_replay_state[
	        OF create_f send_f alphas send_degree create_cp fri final_send replay])
	  have lookup_prefix:
	    "fmlookup (HashMap s_prefix) (QueryIndexChallenge (PQueryCounter s_prefix) (PState s_prefix)) = Some idx"
	  proof -
	    have lookup:
	      "fmlookup (HashMap s_prefix) (QueryIndexChallenge (PQueryCounter s_final) (PState s_final)) = Some idx"
	      using p.hash_extension_lookup[OF query_lookup_replay, of s_prefix] prefix_res
	      by simp
	    then show ?thesis
	      using st_prefix_final q_prefix_replay q_final_replay by simp
	  qed
  from after_prefix obtain idxv_state s_idx where
    rand_v:
      "Some (idxv_state, s_idx) \<in>
        set_dist (execute p.receive_query_index_challenge s_prefix)"
    and after_rand:
      "Some ((fr, as', dg, fl, final, idxv, fv), t) \<in>
        set_dist (execute
          ((let idxv' = p.index (to_nat idxv_state) in
              mmap (v.check_decommit_on_query
                (case out of (fr, as', dg, fl, final) \<Rightarrow> fr) idxv') \<bind>
                (\<lambda>fv. return (case out of (fr, as', dg, fl, final) \<Rightarrow>
                  (fr, as', dg, fl, final, idxv_state, fv))))) s_idx)"
  proof -
    show ?thesis
      using after_prefix
    proof (rule p.set_dist_bindE)
      fix idxv_state s_idx
      assume rand_v:
        "Some (idxv_state, s_idx) \<in>
          set_dist (execute p.receive_query_index_challenge s_prefix)"
        and after_rand:
          "Some ((fr, as', dg, fl, final, idxv, fv), t) \<in>
            set_dist (execute
              ((let idxv' = p.index (to_nat idxv_state) in
                  mmap (v.check_decommit_on_query
                    (case out of (fr, as', dg, fl, final) \<Rightarrow> fr) idxv') \<bind>
                    (\<lambda>fv. return (case out of (fr, as', dg, fl, final) \<Rightarrow>
                      (fr, as', dg, fl, final, idxv_state, fv))))) s_idx)"
      show ?thesis
        by (rule that[OF rand_v after_rand])
    qed
  qed
  have rand_res:
    "idxv_state = idx \<and>
     PState s_idx = PState s_prefix \<and>
     PTranscript s_idx = PTranscript s_prefix \<and>
     s_prefix \<le> s_idx"
    using p.receive_query_index_challenge_known_outcome[OF lookup_prefix rand_v]
    by simp
  have s1_s_idx: "s1 \<le> s_idx"
    using s1_replay prefix_res rand_res by (meson p.hash_ext_trans)
  have tr_idx:
    "PTranscript s_idx =
      query_decommitment_transcript (p.index (to_nat idxv_state)) f_merkle @ rest"
    using rand_res prefix_res idx_def by simp
  have paths:
    "\<And>i. i \<in> set (p.powers_scaled (p.index (to_nat idxv_state))) \<Longrightarrow>
      length (get_authentication_path (length p.f_eval) i f_merkle) =
        floor_log (length p.f_eval)"
    using query_authentication_path_length[OF create_f] by blast
  from after_rand obtain fv0 t0 where
    query_out:
      "Some (fv0, t0) \<in>
        set_dist (execute
          (mmap (v.check_decommit_on_query
            (case out of (fr, as', dg, fl, final) \<Rightarrow> fr)
            (p.index (to_nat idxv_state)))) s_idx)"
    and ret_out:
      "Some ((fr, as', dg, fl, final, idxv, fv), t) \<in>
        set_dist (execute
          (return (case out of (fr, as', dg, fl, final) \<Rightarrow>
            (fr, as', dg, fl, final, idxv_state, fv0))) t0)"
    using rand_res by (auto simp: Let_def elim!: p.set_dist_bindE)
  have query_out_replay:
    "Some (fv0, t0) \<in>
      set_dist (execute
        (mmap (v.check_decommit_on_query
          (case out of (fr, as', dg, fl, final) \<Rightarrow> fr)
          (p.index (to_nat idxv_state))))
        (s_idx\<lparr>
          PTranscript :=
            query_decommitment_transcript (p.index (to_nat idxv_state)) f_merkle @ rest
        \<rparr>))"
  proof -
    have s_idx_update:
      "s_idx\<lparr>
        PTranscript :=
          query_decommitment_transcript (p.index (to_nat idxv_state)) f_merkle @ rest
      \<rparr> = s_idx"
      using tr_idx by simp
    show ?thesis
      using query_out unfolding s_idx_update .
  qed
	  have query_res:
	    "fv0 = map (\<lambda>i. p.f_eval ! i) (p.powers_scaled (p.index (to_nat idxv_state))) \<and>
	     PTranscript t0 = rest \<and>
	     PState t0 =
	       foldl concat (PState s_idx)
	         (query_decommitment_transcript (p.index (to_nat idxv_state)) f_merkle) \<and>
	     s_idx\<lparr>
	       PTranscript :=
	         query_decommitment_transcript (p.index (to_nat idxv_state)) f_merkle @ rest
	     \<rparr> \<le> t0"
    by (rule honest_query_decommitment_replay_outcome[
        OF paths query_out_replay])
  have t_res:
    "(fr, as', dg, fl, final, idxv, fv) =
      (fr0, as0, dg0, fl0, final0, idxv_state, fv0) \<and>
     t = t0"
    using ret_out unfolding out_eq by simp
  have idxv_eq: "idxv = idx"
    using t_res rand_res by simp
  have fv_eq: "fv = map (\<lambda>i. p.f_eval ! i) (p.powers_scaled idx')"
    using t_res query_res rand_res idx_def by simp
  have replay_t: "replay_state \<le> t"
  proof -
    have "s_idx \<le> t0"
    proof -
      have s_idx_update:
        "s_idx\<lparr>
          PTranscript :=
            query_decommitment_transcript (p.index (to_nat idxv_state)) f_merkle @ rest
        \<rparr> = s_idx"
        using tr_idx by simp
      show ?thesis
        using query_res unfolding s_idx_update by simp
    qed
    then show ?thesis
      using prefix_res rand_res t_res by (meson p.hash_ext_trans)
  qed
  show ?thesis
    by (intro conjI exI[where x=roots] exI[where x=challenges] exI[where x=rest])
      (use prefix_res len_roots len_challenges query_res t_res idxv_eq fv_eq replay_t
        replay_prefix roots_aligned successors in simp_all)
qed

end

end
