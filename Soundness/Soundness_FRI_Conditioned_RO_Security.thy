theory Soundness_FRI_Conditioned_RO_Security
  imports
    Stark.Soundness_FRI_Conditioned_RO_Verifier
begin

context soundness
begin

definition
  ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses
where
  "ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses
      A = do {
    (prefix_with_state, data, query_start, raws, query_states) \<leftarrow>
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A;
    attacker_state \<leftarrow> get;
    put
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data));
    verifier_result \<leftarrow> ro_verify_monad_with_fri_prefixes;
    return
      ((((prefix_with_state, data, query_start, raws, query_states),
          attacker_state), fst verifier_result),
        snd verifier_result)
  }"

lemma
  ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses_projection:
  "ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses
      A \<bind>
      (\<lambda>((base, fri_prefixes), result).
        return (base, result)) =
    ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      A"
proof -
  have verifier_projection:
    "\<And>base. ro_verify_monad_with_fri_prefixes \<bind>
        (\<lambda>verifier_result. return (base, snd verifier_result)) =
      ro_verify_monad \<bind>
        (\<lambda>result. return (base, result))"
  proof -
    fix base :: "'b"
    have
      "ro_verify_monad_with_fri_prefixes \<bind>
          (\<lambda>verifier_result. return (base, snd verifier_result)) =
        (ro_verify_monad_with_fri_prefixes \<bind>
          (\<lambda>verifier_result. return (snd verifier_result))) \<bind>
        (\<lambda>result. return (base, result))"
      by (simp add: sm_bind_assoc)
    also have "... =
        ro_verify_monad \<bind>
          (\<lambda>result. return (base, result))"
      by (simp only: ro_verify_monad_with_fri_prefixes_projection)
    finally show
      "ro_verify_monad_with_fri_prefixes \<bind>
          (\<lambda>verifier_result. return (base, snd verifier_result)) =
        ro_verify_monad \<bind>
          (\<lambda>result. return (base, result))"
      .
  qed
  show ?thesis
    unfolding
      ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses_def
      ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
    by (simp add: sm_bind_assoc split_def verifier_projection)
qed

lemma
  ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses_outcomeE:
  assumes outcome:
    "Some
        ((((((prefix, prefix_state), data, query_start, raws, query_states),
             attacker_state), fri_prefixes), result), final_state) \<in>
      set_dist
        (execute
          (ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses
            A)
          initial_state)"
  obtains
    "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          initial_state)"
    "Some ((fri_prefixes, result), final_state) \<in>
      set_dist
        (execute ro_verify_monad_with_fri_prefixes
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
  using outcome
  unfolding
    ro_absorb_checked_staged_security_experiment_with_fri_prefixes_and_query_witnesses_def
  by (auto elim!: set_dist_bindE intro: that)

end

end
