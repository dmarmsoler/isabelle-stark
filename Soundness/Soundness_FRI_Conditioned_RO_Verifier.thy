theory Soundness_FRI_Conditioned_RO_Verifier
  imports
    Stark.Soundness_FRI_Conditioned_RO_Prequery
    Stark.Soundness_FRI_First_Root_RO_Security_Query_Bound
begin

type_synonym 'f fri_ro_prefix_item =
  "(('f protocol_channel \<times> 'f protocol_channel) \<times> ('f \<times> 'f))"

type_synonym 'f fri_ro_prefix_evidence =
  "'f fri_ro_prefix_item list \<times> 'f \<times> 'f fri_ro_prefix_item list"

context soundness
begin

definition ro_verify_after_trace_commits
where
  "ro_verify_after_trace_commits fr trace_commits f_final as = do {
     dg \<leftarrow> protocol_absorb_read;
     assert (to_nat dg \<le> maxDegree);
     composition_commits \<leftarrow>
       ntimes ro_receive_composition_fri_commits
         (ceil_log (to_nat dg + 1));
     final \<leftarrow> protocol_absorb_read;
     ntimes
       (ro_verifier_query_round_program fr trace_commits f_final as
         composition_commits final) rounds
   }"

definition ro_verify_after_trace_commits_with_fri_prefixes
where
  "ro_verify_after_trace_commits_with_fri_prefixes
      fr trace_commits f_final as = do {
     dg \<leftarrow> protocol_absorb_read;
     assert (to_nat dg \<le> maxDegree);
     composition_items \<leftarrow>
       ntimes ro_receive_composition_fri_commits_with_prefix
         (ceil_log (to_nat dg + 1));
     composition_commits \<leftarrow> return (map snd composition_items);
     final \<leftarrow> protocol_absorb_read;
     result \<leftarrow> ntimes
       (ro_verifier_query_round_program fr trace_commits f_final as
         composition_commits final) rounds;
     return ((dg, composition_items), result)
   }"

lemma ro_verify_after_trace_commits_with_fri_prefixes_projection:
  "ro_verify_after_trace_commits_with_fri_prefixes
      fr trace_commits f_final as \<bind>
      (\<lambda>x. return (snd x)) =
    ro_verify_after_trace_commits fr trace_commits f_final as"
proof -
  have comp_projection:
    "\<And>dg. ntimes ro_receive_composition_fri_commits_with_prefix
        (ceil_log (Suc (to_nat dg))) \<bind>
        (\<lambda>items. protocol_absorb_read \<bind>
          (\<lambda>final. ntimes
            (ro_verifier_query_round_program
              fr trace_commits f_final as (map snd items) final)
            rounds)) =
      ntimes ro_receive_composition_fri_commits
        (ceil_log (Suc (to_nat dg))) \<bind>
        (\<lambda>commits. protocol_absorb_read \<bind>
          (\<lambda>final. ntimes
            (ro_verifier_query_round_program
              fr trace_commits f_final as commits final)
            rounds))"
    by (rule
        ntimes_ro_receive_composition_fri_commits_with_prefix_projection_cont)
  show ?thesis
    unfolding ro_verify_after_trace_commits_with_fri_prefixes_def
      ro_verify_after_trace_commits_def
    apply (simp add: sm_bind_assoc)
    apply (rule arg_cong2[where f=sm_bind])
     apply (rule refl)
    apply (rule ext)
    apply (rule arg_cong2[where f=sm_bind])
     apply (rule refl)
    apply (rule ext)
    apply (rule comp_projection)
    done
qed

definition ro_verify_monad_with_fri_prefixes
  :: "(('f fri_ro_prefix_evidence \<times> unit list),
      'f protocol_channel) state_monad"
where
  "ro_verify_monad_with_fri_prefixes = do {
     fr \<leftarrow> protocol_absorb_read;
     trace_items \<leftarrow> ntimes ro_receive_trace_fri_commits_with_prefix
       (ceil_log clength);
     trace_commits \<leftarrow> return (map snd trace_items);
     f_final \<leftarrow> protocol_absorb_read;
     as \<leftarrow> mmap (replicate (length spec) ro_alpha_round);
     tail_result \<leftarrow>
       ro_verify_after_trace_commits_with_fri_prefixes
         fr trace_commits f_final as;
     return
       ((trace_items, fst (fst tail_result), snd (fst tail_result)),
        snd tail_result)
   }"

lemma ro_verify_monad_after_trace_commits:
  "ro_verify_monad = do {
     fr \<leftarrow> protocol_absorb_read;
     trace_commits \<leftarrow> ntimes ro_receive_trace_fri_commits
       (ceil_log clength);
     f_final \<leftarrow> protocol_absorb_read;
     as \<leftarrow> mmap (replicate (length spec) ro_alpha_round);
     ro_verify_after_trace_commits fr trace_commits f_final as
   }"
  unfolding ro_verify_monad_def ro_verify_after_trace_commits_def
  by (simp add: sm_bind_assoc)

lemma ro_verify_monad_with_fri_prefixes_projection:
  "ro_verify_monad_with_fri_prefixes \<bind>
      (\<lambda>x. return (snd x)) =
    ro_verify_monad"
proof -
  have trace_projection:
    "\<And>fr. ntimes ro_receive_trace_fri_commits_with_prefix
        (ceil_log clength) \<bind>
        (\<lambda>items. protocol_absorb_read \<bind>
          (\<lambda>f_final.
            mmap (replicate (length spec) ro_alpha_round) \<bind>
            (\<lambda>as. ro_verify_after_trace_commits
              fr (map snd items) f_final as))) =
      ntimes ro_receive_trace_fri_commits
        (ceil_log clength) \<bind>
        (\<lambda>commits. protocol_absorb_read \<bind>
          (\<lambda>f_final.
            mmap (replicate (length spec) ro_alpha_round) \<bind>
            (\<lambda>as. ro_verify_after_trace_commits
              fr commits f_final as)))"
    by (rule
        ntimes_ro_receive_trace_fri_commits_with_prefix_projection_cont)
  show ?thesis
    unfolding ro_verify_monad_with_fri_prefixes_def
    apply (simp add: sm_bind_assoc
        ro_verify_after_trace_commits_with_fri_prefixes_projection
        ro_verify_monad_after_trace_commits)
    apply (rule arg_cong2[where f=sm_bind])
     apply (rule refl)
    apply (rule ext)
    apply (rule trace_projection)
    done
qed

end

end
