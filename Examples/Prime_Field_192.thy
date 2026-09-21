(*  Title:      Stark/Prime_Field_192.thy
    License:    BSD-3-Clause
*)

theory Prime_Field_192
  imports Prime_192_Certificate Prime_Field_Bridge
begin

section \<open>A certified concrete prime residue field and proper domain\<close>

text \<open>The index type is constructed with exactly the proved prime cardinality.
  No type-class primality assumption remains to discharge for this field.
  The generator is selected once from a proved existence theorem. In
  particular, the primality witness 13 is not assumed to generate the full
  multiplicative group; no executable generator numeral is claimed.\<close>

definition field_cardinality_192 :: nat
  where "field_cardinality_192 = certificate_prime_192"

lemma field_cardinality_192_prime: "prime field_cardinality_192"
  unfolding field_cardinality_192_def by (rule certificate_prime_192_is_prime)

typedef field_index_192 = "{0..<field_cardinality_192}"
  by (rule exI[of _ 0]) (simp add: field_cardinality_192_def certificate_prime_192_def)

lemma CARD_field_index_192 [simp]:
  "CARD(field_index_192)=field_cardinality_192"
  by (simp add: type_definition.card[OF type_definition_field_index_192])

instance field_index_192 :: finite
proof
  have "CARD(field_index_192)>0"
    by (simp add: field_cardinality_192_def certificate_prime_192_def)
  then show "finite (UNIV::field_index_192 set)" by (rule card_ge_0_finite)
qed

instance field_index_192 :: prime_card
  by standard (simp add: field_cardinality_192_prime)

type_synonym field_192 = "field_index_192 mod_ring"

lemma CARD_field_192 [simp]: "CARD(field_192)=field_cardinality_192"
  by simp

lemma field_192_encoding:
  "stark_mod_ring_encode (stark_mod_ring_decode x) = (x::field_192)"
  "range (stark_mod_ring_decode :: field_192 \<Rightarrow> nat) = {0..<field_cardinality_192}"
  by (simp_all add: stark_mod_ring_decode_range)

lemma field_192_decode_encode:
  assumes "n < field_cardinality_192"
  shows "stark_mod_ring_decode (stark_mod_ring_encode n :: field_192)=n"
  by (rule stark_mod_ring_decode_encode) (use assms in simp)

lemma field_192_domain_arithmetic:
  "65536 dvd field_cardinality_192-1"
  "65536<field_cardinality_192-1"
  "2^191 \<le> field_cardinality_192" "field_cardinality_192 < 2^192"
  by (simp_all add: field_cardinality_192_def certificate_prime_192_def)

definition field_generator_192 :: field_192
  where "field_generator_192 = (SOME omega. exact_order omega (field_cardinality_192-1))"

lemma field_generator_192_order:
  "exact_order field_generator_192 (field_cardinality_192-1)"
  unfolding field_generator_192_def
  by (rule someI_ex) (use stark_mod_ring_full_generator_exists[where 'a=field_index_192] in simp)

lemma field_192_domain:
  "field_generator_192 \<noteq> 0"
  "(2::field_192) \<noteq> 0"
  "exact_order (field_generator_192^((field_cardinality_192-1) div 65536)) 65536"
  "field_generator_192 \<notin> set (map ((^) (field_generator_192^((field_cardinality_192-1) div 65536))) [0..<65536])"
proof -
  show "field_generator_192 \<noteq> 0" by (rule stark_exact_order_nonzero[OF field_generator_192_order])
  show "(2::field_192) \<noteq> 0" by (rule stark_mod_ring_two_nonzero)
    (simp add: field_cardinality_192_def certificate_prime_192_def)
  show "exact_order (field_generator_192^((field_cardinality_192-1) div 65536)) 65536"
    by (rule stark_exact_order_divisor[OF field_generator_192_order])
      (use field_192_domain_arithmetic in auto)
  show "field_generator_192 \<notin> set (map ((^) (field_generator_192^((field_cardinality_192-1) div 65536))) [0..<65536])"
    by (rule stark_full_generator_outside_subgroup[OF field_generator_192_order])
      (use field_192_domain_arithmetic in auto)
qed


ML \<open>List.app (Prime_192_Replay_Arithmetic.inspect "concrete field and domain")
  @{thms field_cardinality_192_prime CARD_field_192 field_192_encoding
    field_generator_192_order field_192_domain field_192_domain_arithmetic};\<close>

end
