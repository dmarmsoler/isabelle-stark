(*  Title:      Stark/Soundness_Query_Index_Modulo_Bounds.thy
    License:    BSD-3-Clause
*)

theory Soundness_Query_Index_Modulo_Bounds
  imports Soundness_Core_Events
begin

section \<open>Exact bounds for the modulo query sampler\<close>

text \<open>
  A raw encoding ranges over a finite interval and is then reduced modulo the
  query-space size.  Unless the modulus divides the field size, its residue
  fibers differ by one.  The following arithmetic keeps the quotient and
  remainder correction explicit.
\<close>

definition modulo_max_singleton_fiber :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "modulo_max_singleton_fiber N q =
    N div q + (if N mod q = 0 then 0 else 1)"

definition modulo_preimage_card_envelope :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "modulo_preimage_card_envelope N q k =
    (N div q) * k + min k (N mod q)"

lemma card_modulo_residue_preimage:
  assumes q_pos: "0 < q"
    and b_lt: "b < q"
  shows "card {n. n < N \<and> n mod q = b} =
    N div q + (if b < N mod q then 1 else 0)"
  proof -
  let ?K = "N div q + (if b < N mod q then 1 else 0)"
  let ?S = "{n. n < N \<and> n mod q = b}"
  let ?f = "\<lambda>k. k * q + b"
  have N_eq: "N = (N div q) * q + N mod q"
    using div_mult_mod_eq[of N q] by simp
  have image_eq: "?f ` {..< ?K} = ?S"
  proof (rule equalityI)
    show "?f ` {..< ?K} \<subseteq> ?S"
    proof
      fix n
      assume "n \<in> ?f ` {..< ?K}"
      then obtain k where k_lt: "k < ?K" and n_eq: "n = k * q + b"
        by auto
      have block_lt:
        "k < N div q \<Longrightarrow> k * q + b < (N div q) * q"
      proof -
        assume k_block: "k < N div q"
        have "k * q + b < k * q + q"
          using b_lt by simp
        also have "... = Suc k * q"
          by simp
        also have "... \<le> (N div q) * q"
          by (rule mult_le_mono1) (use k_block in simp)
        finally show ?thesis .
      qed
      have n_lt: "n < N"
      proof (cases "b < N mod q")
        case True
        have k_le: "k \<le> N div q"
          using k_lt True by simp
        show ?thesis
        proof (cases "k < N div q")
          case True
          have "k * q + b < (N div q) * q"
            by (rule block_lt[OF True])
          also have "... \<le> (N div q) * q + N mod q"
            by simp
          also have "... = N"
            using N_eq by simp
          finally show ?thesis
            using n_eq by simp
        next
          case False
          then have k_eq: "k = N div q"
            using k_le by simp
          have "k * q + b < (N div q) * q + N mod q"
            unfolding k_eq using True by linarith
          also have "... = N"
            using N_eq by simp
          finally show ?thesis
            using n_eq by simp
        qed
      next
        case False
        then have k_block: "k < N div q"
          using k_lt by simp
        have "k * q + b < (N div q) * q"
          by (rule block_lt[OF k_block])
        also have "... \<le> (N div q) * q + N mod q"
          by simp
        also have "... = N"
          using N_eq by simp
        finally show ?thesis
          using n_eq by simp
      qed
      moreover have "n mod q = b"
        using n_eq b_lt by simp
      ultimately show "n \<in> ?S"
        by simp
    qed
    show "?S \<subseteq> ?f ` {..< ?K}"
    proof
      fix n
      assume n_in: "n \<in> ?S"
      then have n_lt: "n < N" and n_mod: "n mod q = b"
        by simp_all
      have n_eq: "n = (n div q) * q + b"
        using div_mult_mod_eq[of n q] n_mod by simp
      have n_le: "n \<le> N"
        using n_lt by simp
      have div_le: "n div q \<le> N div q"
        by (rule div_le_mono[OF n_le])
      have k_lt: "n div q < ?K"
      proof (cases "n div q < N div q")
        case True
        then show ?thesis
          by simp
      next
        case False
        then have div_eq: "n div q = N div q"
          using div_le by simp
        have less: "(N div q) * q + b <
            (N div q) * q + N mod q"
        proof -
          have "(N div q) * q + b < N"
            using n_lt n_eq div_eq by simp
          also have "... = (N div q) * q + N mod q"
            by (rule N_eq)
          finally show ?thesis .
        qed
        have b_rem: "b < N mod q"
          using less by linarith
        show ?thesis
          using div_eq b_rem by simp
      qed
      show "n \<in> ?f ` {..< ?K}"
        using n_eq k_lt by auto
    qed
  qed
  have inj: "inj_on ?f {..< ?K}"
    using q_pos unfolding inj_on_def by auto
  have "card ?S = card (?f ` {..< ?K})"
    using image_eq by simp
  also have "... = card {..< ?K}"
    by (rule card_image[OF inj])
  also have "... = ?K"
    by simp
  finally show ?thesis .
qed

lemma modulo_residue_preimage_union:
  assumes subset: "B \<subseteq> {..<q}"
  shows "{n. n < N \<and> n mod q \<in> B} =
    (\<Union>b\<in>B. {n. n < N \<and> n mod q = b})"
  using subset by auto

lemma modulo_residue_preimages_disjoint:
  assumes neq: "b \<noteq> c"
  shows "{n. n < N \<and> n mod q = b} \<inter>
    {n. n < N \<and> n mod q = c} = {}"
  using neq by auto

lemma card_modulo_set_preimage:
  assumes q_pos: "0 < q"
    and subset: "B \<subseteq> {..<q}"
  shows "card {n. n < N \<and> n mod q \<in> B} =
    (N div q) * card B + card (B \<inter> {..<N mod q})"
  proof -
  let ?A = "\<lambda>b. {n. n < N \<and> n mod q = b}"
  have finite_B: "finite B"
    by (rule finite_subset[OF subset]) simp
  have finite_A: "\<forall>b\<in>B. finite (?A b)"
    by simp
  have disjoint:
    "\<forall>b\<in>B. \<forall>c\<in>B. b \<noteq> c \<longrightarrow> ?A b \<inter> ?A c = {}"
    by (auto intro: modulo_residue_preimages_disjoint)
  have preimage_eq:
    "{n. n < N \<and> n mod q \<in> B} = \<Union>(?A ` B)"
    using modulo_residue_preimage_union[OF subset] by simp
  have indicator:
    "(\<Sum>b\<in>B. if b < N mod q then 1 else 0) =
      card (B \<inter> {..<N mod q})"
    using finite_B
  proof (induction B rule: finite_induct)
    case empty
    then show ?case by simp
  next
    case (insert b B)
    show ?case
    proof (cases "b < N mod q")
      case True
      then show ?thesis
        using insert by simp
    next
      case False
      then show ?thesis
        using insert by simp
    qed
  qed
  have "card {n. n < N \<and> n mod q \<in> B} = card (\<Union>(?A ` B))"
    unfolding preimage_eq ..
  also have "... = (\<Sum>b\<in>B. card (?A b))"
    by (rule card_UN_disjoint[OF finite_B finite_A disjoint])
  also have "... =
      (\<Sum>b\<in>B. N div q + (if b < N mod q then 1 else 0))"
  proof (rule sum.cong)
    show "B = B" by simp
    fix b
    assume b_in: "b \<in> B"
    have b_lt: "b < q"
      using subset b_in by auto
    show "card (?A b) =
        N div q + (if b < N mod q then 1 else 0)"
      by (rule card_modulo_residue_preimage[OF q_pos b_lt])
  qed
  also have "... =
      (\<Sum>b\<in>B. N div q) +
      (\<Sum>b\<in>B. if b < N mod q then 1 else 0)"
    by (simp add: sum.distrib)
  also have "... =
      (N div q) * card B + card (B \<inter> {..<N mod q})"
    using indicator by (simp add: mult.commute)
  finally show ?thesis .
qed

lemma card_modulo_set_preimage_le_envelope:
  assumes q_pos: "0 < q"
    and subset: "B \<subseteq> {..<q}"
  shows "card {n. n < N \<and> n mod q \<in> B} \<le>
    modulo_preimage_card_envelope N q (card B)"
proof -
  have finite_B: "finite B"
    by (rule finite_subset[OF subset]) simp
  have card_inter_le_B:
    "card (B \<inter> {..<N mod q}) \<le> card B"
    by (rule card_mono[OF finite_B]) simp
  have card_inter_le_remainder:
    "card (B \<inter> {..<N mod q}) \<le> N mod q"
  proof -
    have "card (B \<inter> {..<N mod q}) \<le> card {..<N mod q}"
      by (rule card_mono) simp_all
    then show ?thesis by simp
  qed
  have card_inter_le:
    "card (B \<inter> {..<N mod q}) \<le> min (card B) (N mod q)"
    using card_inter_le_B card_inter_le_remainder by simp
  have exact:
    "card {n. n < N \<and> n mod q \<in> B} =
      (N div q) * card B + card (B \<inter> {..<N mod q})"
    by (rule card_modulo_set_preimage[OF q_pos subset])
  show ?thesis
    unfolding modulo_preimage_card_envelope_def
    using exact card_inter_le by simp
qed

lemma card_modulo_residue_preimage_le_max:
  assumes q_pos: "0 < q"
    and b_lt: "b < q"
  shows "card {n. n < N \<and> n mod q = b} \<le>
    modulo_max_singleton_fiber N q"
proof -
  have exact:
    "card {n. n < N \<and> n mod q = b} =
      N div q + (if b < N mod q then 1 else 0)"
    by (rule card_modulo_residue_preimage[OF q_pos b_lt])
  show ?thesis
    unfolding modulo_max_singleton_fiber_def
    using exact by (cases "N mod q = 0") simp_all
qed

lemma card_modulo_residue_preimage_dvd:
  assumes q_pos: "0 < q"
    and dvd: "q dvd N"
    and b_lt: "b < q"
  shows "card {n. n < N \<and> n mod q = b} = N div q"
proof -
  have exact:
    "card {n. n < N \<and> n mod q = b} =
      N div q + (if b < N mod q then 1 else 0)"
    by (rule card_modulo_residue_preimage[OF q_pos b_lt])
  show ?thesis
    using exact dvd by (simp add: dvd_eq_mod_eq_0)
qed

lemma modulo_uniform_fraction_cross_le:
  assumes q_pos: "0 < q"
    and k_le: "k \<le> q"
  shows "k * N \<le> q * modulo_preimage_card_envelope N q k"
proof -
  have rem_lt: "N mod q < q"
    by (rule mod_less_divisor[OF q_pos])
  have N_eq: "N = (N div q) * q + N mod q"
    using div_mult_mod_eq[of N q] by simp
  show ?thesis
  proof (cases "k \<le> N mod q")
    case True
    have kr_le: "k * (N mod q) \<le> k * q"
      using rem_lt by simp
    have cross:
      "k * N \<le> q * ((N div q) * k + k)"
    proof -
      have "k * N = k * ((N div q) * q + N mod q)"
        using N_eq by simp
      also have "... =
          k * (N div q) * q + k * (N mod q)"
        by (simp only: distrib_left mult.assoc)
      also have "... \<le> k * (N div q) * q + k * q"
        by (rule add_le_mono[OF order_refl kr_le])
      also have "... = q * ((N div q) * k + k)"
        by (simp only: distrib_left mult.assoc mult.commute)
      finally show ?thesis .
    qed
    show ?thesis
      unfolding modulo_preimage_card_envelope_def min_def
      using True cross by simp
  next
    case False
    have kr_le: "k * (N mod q) \<le> q * (N mod q)"
      using k_le by simp
    have cross:
      "k * N \<le> q * ((N div q) * k + N mod q)"
    proof -
      have "k * N = k * ((N div q) * q + N mod q)"
        using N_eq by simp
      also have "... =
          k * (N div q) * q + k * (N mod q)"
        by (simp only: distrib_left mult.assoc)
      also have "... \<le>
          k * (N div q) * q + q * (N mod q)"
        by (rule add_le_mono[OF order_refl kr_le])
      also have "... = q * ((N div q) * k + N mod q)"
        by (simp only: distrib_left mult.assoc mult.commute)
      finally show ?thesis .
    qed
    show ?thesis
      unfolding modulo_preimage_card_envelope_def min_def
      using False cross by simp
  qed
qed

lemma modulo_uniform_fraction_le_envelope:
  assumes N_pos: "0 < N"
    and q_pos: "0 < q"
    and k_le: "k \<le> q"
  shows "nnreal k / nnreal q \<le>
    nnreal (modulo_preimage_card_envelope N q k) / nnreal N"
proof -
  have cross:
    "k * N \<le> q * modulo_preimage_card_envelope N q k"
    by (rule modulo_uniform_fraction_cross_le[OF q_pos k_le])
  have cross':
    "N * k \<le> q * modulo_preimage_card_envelope N q k"
    using cross by (simp only: mult.commute)
  have cross_real:
    "real (N * k) \<le>
      real (q * modulo_preimage_card_envelope N q k)"
    by (rule of_nat_mono[OF cross'])
  have cross_real':
    "real N * real k \<le>
      real q * real (modulo_preimage_card_envelope N q k)"
    using cross_real by simp
  show ?thesis
    using N_pos q_pos cross_real'
    unfolding NNReal.less_eq_nnreal.rep_eq
      NNReal.less_nnreal.rep_eq
      NNReal.divide_nnreal.rep_eq
      NNReal.times_nnreal.rep_eq
      NNReal.zero_nnreal.rep_eq
      NNReal.nnreal.rep_eq
    by (simp add: field_simps)
qed

context soundness
begin

lemma query_index_nat_preimage_eq_modulo_preimage:
  "query_index_nat_preimage B =
    {n. n < size \<and> n mod query_sample_space_size \<in> B}"
  unfolding query_index_nat_preimage_def to_nat_range
  by auto

lemma card_query_index_nat_preimage_exact:
  assumes subset: "B \<subseteq> query_sample_space"
  shows "card (query_index_nat_preimage B) =
    (size div query_sample_space_size) * card B +
      card (B \<inter> {..<size mod query_sample_space_size})"
proof -
  have subset':
    "B \<subseteq> {..<query_sample_space_size}"
    using subset unfolding query_sample_space_def by auto
  show ?thesis
    unfolding query_index_nat_preimage_eq_modulo_preimage
    by (rule card_modulo_set_preimage[
          OF query_sample_space_size_pos subset'])
qed

lemma card_query_index_raw_preimage_exact:
  assumes subset: "B \<subseteq> query_sample_space"
  shows "card (query_index_raw_preimage B) =
    (size div query_sample_space_size) * card B +
      card (B \<inter> {..<size mod query_sample_space_size})"
  unfolding card_query_index_raw_preimage_eq_nat_preimage
  by (rule card_query_index_nat_preimage_exact[OF subset])

lemma card_query_index_nat_preimage_le_envelope:
  assumes subset: "B \<subseteq> query_sample_space"
  shows "card (query_index_nat_preimage B) \<le>
    modulo_preimage_card_envelope
      size query_sample_space_size (card B)"
proof -
  have subset':
    "B \<subseteq> {..<query_sample_space_size}"
    using subset unfolding query_sample_space_def by auto
  show ?thesis
    unfolding query_index_nat_preimage_eq_modulo_preimage
    by (rule card_modulo_set_preimage_le_envelope[
          OF query_sample_space_size_pos subset'])
qed

lemma card_query_index_raw_preimage_le_envelope:
  assumes subset: "B \<subseteq> query_sample_space"
  shows "card (query_index_raw_preimage B) \<le>
    modulo_preimage_card_envelope
      size query_sample_space_size (card B)"
  unfolding card_query_index_raw_preimage_eq_nat_preimage
  by (rule card_query_index_nat_preimage_le_envelope[OF subset])

lemma query_raw_preimage_card_envelope_eq_modulo:
  "query_raw_preimage_card_envelope k =
    modulo_preimage_card_envelope size query_sample_space_size k"
  unfolding query_raw_preimage_card_envelope_def
    modulo_preimage_card_envelope_def
  by simp

lemma query_raw_preimage_card_envelope_mono:
  assumes kl: "k \<le> l"
  shows "query_raw_preimage_card_envelope k \<le>
    query_raw_preimage_card_envelope l"
proof -
  have mult_le:
    "(size div query_sample_space_size) * k \<le>
      (size div query_sample_space_size) * l"
    using kl by simp
  have min_le:
    "min k (size mod query_sample_space_size) \<le>
      min l (size mod query_sample_space_size)"
    using kl by simp
  show ?thesis
    unfolding query_raw_preimage_card_envelope_def
    using mult_le min_le by linarith
qed

lemma query_raw_preimage_card_envelope_query_sample_space[simp]:
  "query_raw_preimage_card_envelope query_sample_space_size = size"
proof -
  have remainder_lt:
    "size mod query_sample_space_size < query_sample_space_size"
    by (simp add: query_sample_space_size_pos)
  have size_eq:
    "size =
      (size div query_sample_space_size) * query_sample_space_size +
        size mod query_sample_space_size"
    using div_mult_mod_eq[of size query_sample_space_size] by simp
  show ?thesis
    unfolding query_raw_preimage_card_envelope_def
    using remainder_lt size_eq by simp
qed

lemma query_raw_preimage_card_envelope_le_size:
  assumes "k \<le> query_sample_space_size"
  shows "query_raw_preimage_card_envelope k \<le> size"
  using query_raw_preimage_card_envelope_mono[OF assms] by simp

lemma query_uniform_fraction_le_query_envelope:
  assumes k_le: "k \<le> query_sample_space_size"
  shows "nnreal k / nnreal query_sample_space_size \<le>
    nnreal (query_raw_preimage_card_envelope k) / nnreal size"
proof -
  have size_pos: "0 < size"
    using size_card by simp
  show ?thesis
    unfolding query_raw_preimage_card_envelope_eq_modulo
    by (rule modulo_uniform_fraction_le_envelope[
          OF size_pos query_sample_space_size_pos k_le])
qed


lemma card_query_index_raw_preimage_le_query_envelope:
  assumes subset: "B \<subseteq> query_sample_space"
  shows "card (query_index_raw_preimage B) \<le>
    query_raw_preimage_card_envelope (card B)"
  unfolding query_raw_preimage_card_envelope_eq_modulo
  by (rule card_query_index_raw_preimage_le_envelope[OF subset])

lemma query_index_raw_preimage_probability_le_envelope:
  assumes subset: "B \<subseteq> query_sample_space"
  shows "nnreal (card (query_index_raw_preimage B)) / nnreal size \<le>
    nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size"
  by (rule nnreal_nat_divide_right_mono[
        OF card_query_index_raw_preimage_le_query_envelope[OF subset]])

lemma query_index_raw_preimage_probability_le_query_error_bound:
  assumes subset: "B \<subseteq> query_sample_space"
    and card_le: "card B \<le> query_agreement_bound"
  shows "nnreal (card (query_index_raw_preimage B)) / nnreal size \<le>
    query_error_bound"
proof -
  have envelope_le:
    "query_raw_preimage_card_envelope (card B) \<le>
      query_raw_preimage_card_envelope query_agreement_bound"
    by (rule query_raw_preimage_card_envelope_mono[OF card_le])
  have "nnreal (card (query_index_raw_preimage B)) / nnreal size \<le>
      nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size"
    by (rule query_index_raw_preimage_probability_le_envelope[OF subset])
  also have "... \<le>
      nnreal (query_raw_preimage_card_envelope query_agreement_bound) /
        nnreal size"
    by (rule nnreal_nat_divide_right_mono[OF envelope_le])
  also have "... = query_error_bound"
    unfolding query_error_bound_def ..
  finally show ?thesis .
qed

lemma query_uniform_fraction_le_query_error_bound:
  assumes k_le: "k \<le> query_agreement_bound"
  shows "nnreal k / nnreal query_sample_space_size \<le> query_error_bound"
proof -
  have agreement_lt:
    "query_agreement_bound < query_sample_space_size"
    by (rule spec_degree_wellformed_query_margin[
          OF spec_degree_wellformed_from_spec_query_margin])
  have k_query_le: "k \<le> query_sample_space_size"
    using k_le agreement_lt by linarith
  have envelope_le:
    "query_raw_preimage_card_envelope k \<le>
      query_raw_preimage_card_envelope query_agreement_bound"
    by (rule query_raw_preimage_card_envelope_mono[OF k_le])
  have "nnreal k / nnreal query_sample_space_size \<le>
      nnreal (query_raw_preimage_card_envelope k) / nnreal size"
    by (rule query_uniform_fraction_le_query_envelope[OF k_query_le])
  also have "... \<le>
      nnreal (query_raw_preimage_card_envelope query_agreement_bound) /
        nnreal size"
    by (rule nnreal_nat_divide_right_mono[OF envelope_le])
  also have "... = query_error_bound"
    unfolding query_error_bound_def ..
  finally show ?thesis .
qed

lemma query_raw_preimage_card_envelope_probability_le_query_error_bound:
  assumes k_le: "k \<le> query_agreement_bound"
  shows "nnreal (query_raw_preimage_card_envelope k) / nnreal size \<le>
    query_error_bound"
proof -
  have envelope_le:
    "query_raw_preimage_card_envelope k \<le>
      query_raw_preimage_card_envelope query_agreement_bound"
    by (rule query_raw_preimage_card_envelope_mono[OF k_le])
  have "nnreal (query_raw_preimage_card_envelope k) / nnreal size \<le>
      nnreal (query_raw_preimage_card_envelope query_agreement_bound) /
        nnreal size"
    by (rule nnreal_nat_divide_right_mono[OF envelope_le])
  then show ?thesis
    unfolding query_error_bound_def .
qed



lemma card_query_index_raw_singleton_preimage_exact:
  assumes idx_in: "idx \<in> query_sample_space"
  shows "card (query_index_raw_preimage {idx}) =
    size div query_sample_space_size +
      (if idx < size mod query_sample_space_size then 1 else 0)"
proof -
  have singleton_subset: "{idx} \<subseteq> query_sample_space"
    using idx_in by simp
  show ?thesis
    using card_query_index_raw_preimage_exact[OF singleton_subset]
    by simp
qed

lemma card_query_index_raw_singleton_preimage_le_max:
  assumes idx_in: "idx \<in> query_sample_space"
  shows "card (query_index_raw_preimage {idx}) \<le>
    modulo_max_singleton_fiber size query_sample_space_size"
proof -
  have exact:
    "card (query_index_raw_preimage {idx}) =
      size div query_sample_space_size +
        (if idx < size mod query_sample_space_size then 1 else 0)"
    by (rule card_query_index_raw_singleton_preimage_exact[OF idx_in])
  show ?thesis
    unfolding modulo_max_singleton_fiber_def
    using exact by (cases "size mod query_sample_space_size = 0") simp_all
qed

text \<open>The divisible formula is retained only as a diagnostic corollary.
The live sampler bounds above account explicitly for the remainder.\<close>

lemma card_query_index_raw_preimage_divisible:
  assumes dvd: "query_sample_space_size dvd size"
    and subset: "B \<subseteq> query_sample_space"
  shows "card (query_index_raw_preimage B) =
    (size div query_sample_space_size) * card B"
proof -
  have exact:
    "card (query_index_raw_preimage B) =
      (size div query_sample_space_size) * card B +
        card (B \<inter> {..<size mod query_sample_space_size})"
    by (rule card_query_index_raw_preimage_exact[OF subset])
  show ?thesis
    using exact dvd by (simp add: dvd_eq_mod_eq_0)
qed

text \<open>
  A false statement cannot coexist with a singleton query space.  If the query
  space had size one, the specification margin would force every constraint
  root list to be empty, and the zero polynomial would be a valid trace.
\<close>

lemma not_exists_valid_trace_imp_query_sample_space_size_gt_one:
  assumes false_statement: "\<not> exists_valid_trace"
  shows "1 < query_sample_space_size"
proof (rule ccontr)
  assume not_gt: "\<not> 1 < query_sample_space_size"
  have query_size_one: "query_sample_space_size = 1"
    using query_sample_space_size_pos not_gt by linarith
  have roots_sum_zero:
      "sum_list (map (\<lambda>(_, roots, _). length roots) spec) = 0"
    using spec_query_margin
    unfolding query_sample_space_size_def[symmetric]
    using query_size_one by linarith
  have roots_empty:
      "\<And>c roots d. (c, roots, d) \<in> set spec \<Longrightarrow> roots = []"
  proof -
    fix c roots d
    assume entry: "(c, roots, d) \<in> set spec"
    show "roots = []"
      using roots_sum_zero entry
      by (induction spec) auto
  qed
  have zero_low_degree: "degree (0 :: 'f poly) < clength"
    using clength_pos by simp
  have zero_satisfies:
      "\<And>c roots d. (c, roots, d) \<in> set spec \<Longrightarrow>
        trace_satisfies_constraint (0 :: 'f poly) c roots"
  proof -
    fix c roots d
    assume entry: "(c, roots, d) \<in> set spec"
    have "roots = []"
      by (rule roots_empty[OF entry])
    then show "trace_satisfies_constraint (0 :: 'f poly) c roots"
      unfolding trace_satisfies_constraint_def by simp
  qed
  have "exists_valid_trace"
    by (rule exists_valid_traceI[OF zero_low_degree zero_satisfies])
  then show False
    using false_statement by contradiction
qed

end

end
