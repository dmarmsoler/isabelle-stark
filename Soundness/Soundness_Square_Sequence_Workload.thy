(*  Title:      Stark/Soundness_Square_Sequence_Workload.thy
    License:    BSD-3-Clause
*)

theory Soundness_Square_Sequence_Workload
  imports Soundness_Core_Base Stark_Examples.Square_Sequence_Workload
begin

section \<open>Square-sequence workload and the existing soundness locale\<close>

text \<open>These facts connect the scalable specification to the existing valid-trace
  predicate. They do not redefine acceptance, restrict the adversary, add
  public soundness premises, or certify a concrete error target. In particular,
  interpolation completeness and authenticated execution construction remain
  separate from the soundness-direction computation relation proved here.\<close>

subsection \<open>Semantic and metadata consequences\<close>

context soundness
begin

lemma square_workload_valid_trace_endpoint:
  assumes schema: "spec=square_workload_spec clength a z" and two: "powers=2"
    and valid: exists_valid_trace
  shows "z=a^(2^(clength-1))"
proof -
  obtain f where constraints: "\<forall>(c,roots,d)\<in>set spec. trace_satisfies_constraint f c roots"
    using valid unfolding exists_valid_trace_def by blast
  show ?thesis
    by (rule square_workload_endpoint[where f=f and g=g])
      (use constraints[unfolded trace_satisfies_constraint_def trace_powers_of_def] in \<open>simp add: schema two\<close>)
qed

lemma square_workload_true_statement:
  assumes schema: "spec=square_workload_spec clength 1 1" and two: "powers=2"
  shows exists_valid_trace
proof -
  have witness: "degree (1::'f poly)<clength \<and>
    (\<forall>(c,roots,d)\<in>set spec. trace_satisfies_constraint 1 c roots)"
    using square_workload_one_witness[OF clength_pos, of g]
    unfolding trace_satisfies_constraint_def trace_powers_of_def
    by (auto simp only: schema two)
  show ?thesis unfolding exists_valid_trace_def using witness by blast
qed

lemma square_workload_false_statement:
  assumes schema: "spec=square_workload_spec clength 1 0" and two: "powers=2"
  shows "\<not>exists_valid_trace"
  using square_workload_valid_trace_endpoint[OF schema two] by auto

lemma square_workload_query_size:
  assumes "powers=2"
  shows "query_sample_space_size=clength*scale-scale"
  unfolding query_sample_space_size_def using assms by (simp add: numeral_2_eq_2)

lemma square_workload_all_roots:
  assumes schema: "spec=square_workload_spec clength a z" and two: "powers=2"
  shows "set all_constraint_roots = (^) g ` {0..<clength}"
proof -
  have L: "2\<le>clength" using powers_le_clength two by simp
  have indices: "{0,clength-1} \<union> {0..<clength-1} = {0..<clength}"
    using L by auto
  have raw: "set all_constraint_roots = (^) g ` ({0,clength-1} \<union> {0..<clength-1})"
    unfolding all_constraint_roots_def
    by (simp only: set_remdups)
      (simp add: schema g_map_def square_workload_spec_def)
  show ?thesis using raw by (simp only: indices)
qed

lemma square_workload_all_roots_length:
  assumes schema: "spec=square_workload_spec clength a z" and two: "powers=2"
  shows "length all_constraint_roots=clength"
proof -
  have inj: "inj_on ((^) g) {0..<clength}"
    by (rule inj_onI) (auto intro: g_power_inj_on_range)
  have dist: "distinct all_constraint_roots" by (simp add: all_constraint_roots_def)
  have "length all_constraint_roots=card (set all_constraint_roots)"
    by (rule distinct_card[OF dist, symmetric])
  also have "...=card ((^) g ` {0..<clength})"
    by (simp only: square_workload_all_roots[OF schema two])
  also have "...=clength" using inj by (simp add: card_image)
  finally show ?thesis .
qed

lemma square_workload_reference_metadata:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
  shows "maxDegree=1023"
    and "length all_constraint_roots=1024"
    and "query_sample_space_size=65472"
    and "query_agreement_bound=2047"
proof -
  show maxdeg: "maxDegree=1023"
    unfolding maxDegree_def using schema geometry
    by (simp add: square_workload_max_degree)
  show roots: "length all_constraint_roots=1024"
    using square_workload_all_roots_length[OF schema geometry(3)] geometry by simp
  show "query_sample_space_size=65472"
    using square_workload_query_size[OF geometry(3)] geometry by simp
  show "query_agreement_bound=2047"
    unfolding query_agreement_bound_def using maxdeg roots by simp
qed

end

subsection \<open>Discharging the inherited soundness obligations\<close>

text \<open>The inequality below is exactly the existing specification query margin
  specialized to this schema: its two sides are 2L and (L-1)S. It is an explicit
  arithmetic obligation, not a new locale premise. Positive repetitions are
  required by the existing soundness locale.\<close>

theorem square_workload_mod_ring_soundness:
  fixes omega a z :: "'a::prime_card mod_ring"
  assumes L: "2\<le>L" "\<exists>k. L=2^k" and S: "\<exists>k. S=2^k"
    and order: "exact_order omega (CARD('a)-1)"
    and domain: "L*S dvd CARD('a)-1" "L*S<CARD('a)-1"
    and R: "0<R" and margin: "2*L<(L-1)*S"
  shows "soundness omega omega S L 2
    stark_mod_ring_decode stark_mod_ring_encode CARD('a)
    (square_workload_spec L a z) R (square_workload_spec2 L a z)"
proof (rule soundness.intro)
  show "verifier omega omega S L 2
    stark_mod_ring_decode stark_mod_ring_encode CARD('a)
    (square_workload_spec L a z) (square_workload_spec2 L a z)"
    by (rule square_workload_mod_ring_verifier[OF L S order domain])
  show "soundness_axioms S L 2 (square_workload_spec L a z) R"
  proof (rule soundness_axioms.intro)
    show "0<R" by (rule R)
    have lhs: "Max (degrees L (square_workload_spec L a z))+
      sum_list (map (\<lambda>(_,roots,_). length roots) (square_workload_spec L a z)) = 2*L"
      using L by (simp add: square_workload_max_degree square_workload_root_sum)
    have rhs: "L*S-Max (set [0..<2])*S = (L-1)*S"
      by (simp add: numeral_2_eq_2 diff_mult_distrib)
    show "Max (degrees L (square_workload_spec L a z))+
      sum_list (map (\<lambda>(_,roots,_). length roots) (square_workload_spec L a z))
      < L*S-Max (set [0..<2])*S"
      unfolding lhs rhs by (rule margin)
  qed
qed

corollary square_workload_mod_ring_soundness_exists:
  fixes a z :: "'a::prime_card mod_ring"
  assumes L: "2\<le>L" "\<exists>k. L=2^k" and S: "\<exists>k. S=2^k"
    and domain: "L*S dvd CARD('a)-1" "L*S<CARD('a)-1"
    and R: "0<R" and margin: "2*L<(L-1)*S"
  shows "\<exists>omega::'a mod_ring. soundness omega omega S L 2
    stark_mod_ring_decode stark_mod_ring_encode CARD('a)
    (square_workload_spec L a z) R (square_workload_spec2 L a z)"
  using stark_mod_ring_full_generator_exists[where 'a='a]
    square_workload_mod_ring_soundness[OF L S _ domain R margin, where a=a and z=z]
  by blast

text \<open>At length 1024 and scale 64, only the displayed field/domain and positive
  repetition conditions remain for this interpretation. No particular field
  cardinality or cryptographic security claim is supplied by this corollary.\<close>

corollary square_workload_reference_soundness_exists:
  fixes a z :: "'a::prime_card mod_ring"
  assumes "65536 dvd CARD('a)-1" "65536<CARD('a)-1" "0<R"
  shows "\<exists>omega::'a mod_ring. soundness omega omega 64 1024 2
    stark_mod_ring_decode stark_mod_ring_encode CARD('a)
    (square_workload_spec 1024 a z) R (square_workload_spec2 1024 a z)"
proof (rule square_workload_mod_ring_soundness_exists)
  show "2\<le>(1024::nat)" by simp
  show "\<exists>k. (1024::nat)=2^k" by (rule exI[of _ 10]) simp
  show "\<exists>k. (64::nat)=2^k" by (rule exI[of _ 6]) simp
  show "1024*64 dvd CARD('a)-1" using assms by simp
  show "1024*64<CARD('a)-1" using assms by simp
  show "0<R" by (rule assms(3))
  show "(2::nat)*1024<(1024-1)*64" by simp
qed

subsection \<open>A shared domain and genuine true and false statements\<close>

text \<open>The generator/domain can be chosen once for every pair of endpoints.
  The final theorem interprets the existing locale twice on that same domain:
  endpoints one/one have a valid constant trace, whereas one/zero do not.
  The compatibility operation and legacy error parameters remain arbitrary;
  they impose no opening-stage or adversarial query-budget restriction.\<close>

theorem square_workload_common_soundness_domain:
  assumes L: "2\<le>L" "\<exists>k. L=2^k" and S: "\<exists>k. S=2^k"
    and domain: "L*S dvd CARD('a::prime_card)-1" "L*S<CARD('a)-1"
    and R: "0<R" and margin: "2*L<(L-1)*S"
  obtains omega :: "'a::prime_card mod_ring"
    where "\<And>a z. soundness omega omega S L 2
      stark_mod_ring_decode stark_mod_ring_encode CARD('a)
      (square_workload_spec L a z) R (square_workload_spec2 L a z)"
proof -
  obtain omega :: "'a mod_ring" where order: "exact_order omega (CARD('a)-1)"
    using stark_mod_ring_full_generator_exists[where 'a='a] by blast
  show thesis by (rule that[of omega])
    (rule square_workload_mod_ring_soundness[OF L S order domain R margin])
qed

lemma square_workload_prime_field_endpoint:
  fixes combine :: "'a::prime_card mod_ring \<Rightarrow> 'a mod_ring \<Rightarrow> 'a mod_ring"
    and omega a z :: "'a mod_ring"
    and et ec em :: prob and R :: nat
  assumes L: "2\<le>L" "\<exists>k. L=2^k" and S: "\<exists>k. S=2^k"
    and order: "exact_order omega (CARD('a)-1)"
    and domain: "L*S dvd CARD('a)-1" "L*S<CARD('a)-1"
    and R: "0<R" and margin: "2*L<(L-1)*S"
  shows "soundness.exists_valid_trace omega L 2 CARD('a) (square_workload_spec L a z)
    \<longrightarrow> z=a^(2^(L-1))"
proof -
  interpret workload: soundness combine omega omega S L 2
    stark_mod_ring_decode stark_mod_ring_encode "CARD('a)"
    "square_workload_spec L a z" R "square_workload_spec2 L a z" et ec em
    by (rule square_workload_mod_ring_soundness[OF L S order domain R margin])
  show ?thesis using workload.square_workload_valid_trace_endpoint by blast
qed

theorem square_workload_prime_field_nonvacuity:
  fixes combine :: "'a::prime_card mod_ring \<Rightarrow> 'a mod_ring \<Rightarrow> 'a mod_ring"
    and et ec em :: prob and R :: nat
  assumes L: "2\<le>L" "\<exists>k. L=2^k" and S: "\<exists>k. S=2^k"
    and domain: "L*S dvd CARD('a)-1" "L*S<CARD('a)-1"
    and R: "0<R" and margin: "2*L<(L-1)*S"
  obtains omega :: "'a::prime_card mod_ring"
    where "\<And>a z. soundness omega omega S L 2
      stark_mod_ring_decode stark_mod_ring_encode CARD('a)
      (square_workload_spec L a z) R (square_workload_spec2 L a z)"
    and "soundness.exists_valid_trace omega L 2 CARD('a) (square_workload_spec L 1 1)"
    and "\<not>soundness.exists_valid_trace omega L 2 CARD('a) (square_workload_spec L 1 0)"
proof -
  obtain omega :: "'a mod_ring" where instantiated:
    "\<And>a z. soundness omega omega S L 2
      stark_mod_ring_decode stark_mod_ring_encode CARD('a)
      (square_workload_spec L a z) R (square_workload_spec2 L a z)"
    by (rule square_workload_common_soundness_domain[OF L S domain R margin]) blast
  interpret yes: soundness combine omega omega S L 2
    stark_mod_ring_decode stark_mod_ring_encode "CARD('a)"
    "square_workload_spec L 1 1" R "square_workload_spec2 L 1 1" et ec em
    by (rule instantiated)
  interpret no: soundness combine omega omega S L 2
    stark_mod_ring_decode stark_mod_ring_encode "CARD('a)"
    "square_workload_spec L 1 0" R "square_workload_spec2 L 1 0" et ec em
    by (rule instantiated)
  show thesis
    by (rule that[OF instantiated yes.square_workload_true_statement no.square_workload_false_statement])
      simp_all
qed

end
