(*  Title:      Stark/Completeness_Replay.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Completeness_Replay
  imports Completeness_Transcript
begin

section \<open>Verifier Replay\<close>

text \<open>Verifier replay of honest root, alpha, degree, and FRI-prefix transcript phases.\<close>

context verification
begin

lemma verifier_replay_root_alpha_degree_prefix:
  assumes prefix:
    "PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
    and later: "transcript_extends prover_state s4"
    and replay: "replay_state = verifier_replay_state prover_state"
  shows "\<exists>rest.
    PTranscript replay_state = value f_merkle # as @ [of_nat (degree cp')] @ rest"
proof -
  from later obtain xs where
    tr_final: "PTranscript prover_state = xs @ PTranscript s4"
    unfolding transcript_extends_def by auto
  have "PTranscript replay_state =
      rev (xs @ (of_nat (degree cp') # rev as @ [value f_merkle]))"
    using replay tr_final prefix
    unfolding verifier_replay_state_def by simp
  also have "... = value f_merkle # as @ [of_nat (degree cp')] @ rev xs"
    by simp
  finally show ?thesis by blast
qed

lemma verifier_root_read_from_replay_prefix:
  assumes prefix:
    "PTranscript replay_state = value f_merkle # as @ [of_nat (degree cp')] @ rest"
    and read_fr:
      "Some (fr, s1) \<in> set_dist (execute p.read replay_state)"
  shows
    "fr = value f_merkle \<and>
     PTranscript s1 = as @ [of_nat (degree cp')] @ rest"
proof -
  have start_eq:
    "replay_state =
      replay_state\<lparr>PTranscript := value f_merkle # (as @ [of_nat (degree cp')] @ rest)\<rparr>"
    using prefix by simp
  have read_start:
    "Some (fr, s1) \<in>
      set_dist (execute p.read
        (replay_state\<lparr>
          PTranscript := value f_merkle # (as @ [of_nat (degree cp')] @ rest)\<rparr>))"
    by (subst start_eq[symmetric]) (rule read_fr)
  have replay:
    "fr = value f_merkle \<and>
     s1 = replay_state\<lparr>
       PState := concat (PState replay_state) (value f_merkle),
       PTranscript := as @ [of_nat (degree cp')] @ rest\<rparr>"
    by (rule p.read_cons_outcome[OF read_start])
  then show ?thesis by simp
qed

lemma honest_root_alpha_degree_prefix_no_failure:
  assumes htv: "honest_trace_valid"
    and len_as: "length as = length spec"
    and prefix:
      "PTranscript replay_state =
        value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @ rest"
    and lookups:
      "\<forall>i < length as.
        fmlookup (HashMap replay_state)
          (AlphaChallenge (PAlphaCounter replay_state + i)
            (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
          Some (as ! i)"
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
        return (fr, as', dg)
      }) replay_state))"
proof -
  let ?dg = "of_nat (degree (p.cp as p.f_powers))"
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  show ?thesis
  proof (rule no_failure_bindI)
    show "None \<notin> dom (dist (execute p.read replay_state))"
      by (rule p.read_no_failure) (use prefix in simp)
  next
    fix fr s1
    assume read_fr: "Some (fr, s1) \<in> set_dist (execute p.read replay_state)"
    have read_start:
      "Some (fr, s1) \<in>
        set_dist (execute p.read
          (replay_state\<lparr>PTranscript := value f_merkle # (as @ [?dg] @ rest)\<rparr>))"
    proof -
      have start_eq:
        "replay_state =
          replay_state\<lparr>PTranscript := value f_merkle # (as @ [?dg] @ rest)\<rparr>"
        using prefix by simp
      show ?thesis
        by (subst start_eq[symmetric]) (rule read_fr)
    qed
    have read_res:
      "fr = value f_merkle \<and>
       s1 =
         replay_state\<lparr>
           PState := concat (PState replay_state) (value f_merkle),
           PTranscript := as @ [?dg] @ rest\<rparr>"
      using p.read_cons_outcome[OF read_start] by simp
    have alpha_lookups:
      "\<forall>i < length as.
        fmlookup (HashMap s1)
          (AlphaChallenge (PAlphaCounter s1 + i)
            (foldl concat (PState s1) (take i as))) = Some (as ! i)"
      using lookups read_res by simp
    have alpha_nf:
      "None \<notin> dom (dist (execute
        (mmap (replicate (length spec) ?round)) s1))"
    proof -
      have s1_update: "s1\<lparr>PTranscript := as @ [?dg] @ rest\<rparr> = s1"
        using read_res by simp
      have nf:
        "None \<notin> dom (dist (execute
          (mmap (replicate (length as) ?round))
          (s1\<lparr>PTranscript := as @ [?dg] @ rest\<rparr>)))"
        using honest_alpha_mmap_replay_no_failure[OF alpha_lookups, of "?dg # rest"]
        by simp
      show ?thesis
        using nf unfolding len_as[symmetric] s1_update .
    qed
    show "None \<notin> dom (dist (execute
      (mmap (replicate (length spec) ?round) \<bind>
        (\<lambda>as'. p.read \<bind>
          (\<lambda>dg. assert (to_nat dg \<le> p.maxDegree) \<bind>
            (\<lambda>_. return (fr, as', dg)))))
      s1))"
    proof (rule no_failure_bindI[OF alpha_nf])
      fix as' s2
      assume alpha_out:
        "Some (as', s2) \<in>
          set_dist (execute (mmap (replicate (length spec) ?round)) s1)"
      have s1_update: "s1\<lparr>PTranscript := as @ [?dg] @ rest\<rparr> = s1"
        using read_res by simp
      have alpha_out':
        "Some (as', s2) \<in>
          set_dist (execute (mmap (replicate (length as) ?round))
            (s1\<lparr>PTranscript := as @ [?dg] @ rest\<rparr>))"
        using alpha_out unfolding len_as[symmetric] s1_update .
      have alpha_res:
        "as' = as \<and>
         PState s2 = foldl concat (PState s1) as \<and>
         PTranscript s2 = ?dg # rest \<and>
         s1 \<le> s2"
        using honest_alpha_mmap_replay_outcome[OF alpha_lookups alpha_out'] by simp
      show "None \<notin> dom (dist (execute
        (p.read \<bind>
          (\<lambda>dg. assert (to_nat dg \<le> p.maxDegree) \<bind>
            (\<lambda>_. return (fr, as', dg)))) s2))"
      proof (rule no_failure_bindI)
        show "None \<notin> dom (dist (execute p.read s2))"
          by (rule p.read_no_failure) (use alpha_res in simp)
      next
        fix dg s3
        assume read_dg: "Some (dg, s3) \<in> set_dist (execute p.read s2)"
        have read_dg_start:
          "Some (dg, s3) \<in>
            set_dist (execute p.read (s2\<lparr>PTranscript := ?dg # rest\<rparr>))"
        proof -
          have s2_update: "s2 = s2\<lparr>PTranscript := ?dg # rest\<rparr>"
            using alpha_res by simp
          show ?thesis
            by (subst s2_update[symmetric]) (rule read_dg)
        qed
        have dg_res:
          "dg = ?dg \<and>
           s3 = s2\<lparr>PState := concat (PState s2) ?dg, PTranscript := rest\<rparr>"
          using p.read_cons_outcome[OF read_dg_start] by simp
        have degree_ok: "to_nat dg \<le> p.maxDegree"
          using honest_degree_message_assert_hol[OF htv, of as] dg_res by simp
        show "None \<notin> dom (dist (execute
          (assert (to_nat dg \<le> p.maxDegree) \<bind> (\<lambda>_. return (fr, as', dg))) s3))"
          using degree_ok by (simp add: assert_def)
      qed
    qed
  qed
qed

lemma honest_root_alpha_degree_prefix_outcome:
  assumes htv: "honest_trace_valid"
    and len_as: "length as = length spec"
    and prefix:
      "PTranscript replay_state =
        value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @ rest"
    and lookups:
      "\<forall>i < length as.
        fmlookup (HashMap replay_state)
          (AlphaChallenge (PAlphaCounter replay_state + i)
            (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
          Some (as ! i)"
    and outcome:
      "Some ((fr, as', dg), t) \<in> set_dist (execute
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
          return (fr, as', dg)
        }) replay_state)"
  shows
    "fr = value f_merkle \<and>
     as' = as \<and>
     dg = of_nat (degree (p.cp as p.f_powers)) \<and>
     PState t =
       concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
         (of_nat (degree (p.cp as p.f_powers))) \<and>
     PTranscript t = rest \<and>
     replay_state \<le> t"
proof -
  let ?dg = "of_nat (degree (p.cp as p.f_powers))"
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  from outcome obtain s1 s2 s3 where
    read_fr: "Some (fr, s1) \<in> set_dist (execute p.read replay_state)"
    and alphas:
      "Some (as', s2) \<in>
        set_dist (execute (mmap (replicate (length spec) ?round)) s1)"
    and read_dg: "Some (dg, s3) \<in> set_dist (execute p.read s2)"
    and degree_assert:
      "Some ((), t) \<in> set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s3)"
    by (auto elim!: p.set_dist_bindE)
  have read_start:
    "Some (fr, s1) \<in>
      set_dist (execute p.read
        (replay_state\<lparr>PTranscript := value f_merkle # (as @ [?dg] @ rest)\<rparr>))"
  proof -
    have start_eq:
      "replay_state =
        replay_state\<lparr>PTranscript := value f_merkle # (as @ [?dg] @ rest)\<rparr>"
      using prefix by simp
    show ?thesis
      by (subst start_eq[symmetric]) (rule read_fr)
  qed
  have read_res:
    "fr = value f_merkle \<and>
     s1 =
       replay_state\<lparr>
         PState := concat (PState replay_state) (value f_merkle),
         PTranscript := as @ [?dg] @ rest\<rparr>"
    using p.read_cons_outcome[OF read_start] by simp
  have alpha_lookups:
    "\<forall>i < length as.
      fmlookup (HashMap s1)
        (AlphaChallenge (PAlphaCounter s1 + i)
          (foldl concat (PState s1) (take i as))) = Some (as ! i)"
    using lookups read_res by simp
  have s1_update: "s1\<lparr>PTranscript := as @ [?dg] @ rest\<rparr> = s1"
    using read_res by simp
  have alpha_out:
    "Some (as', s2) \<in>
      set_dist (execute (mmap (replicate (length as) ?round))
        (s1\<lparr>PTranscript := as @ [?dg] @ rest\<rparr>))"
    using alphas unfolding len_as[symmetric] s1_update .
  have alpha_res:
    "as' = as \<and>
     PState s2 = foldl concat (PState s1) as \<and>
     PTranscript s2 = ?dg # rest \<and>
     s1 \<le> s2"
    using honest_alpha_mmap_replay_outcome[OF alpha_lookups alpha_out] by simp
  have read_dg_start:
    "Some (dg, s3) \<in>
      set_dist (execute p.read (s2\<lparr>PTranscript := ?dg # rest\<rparr>))"
  proof -
    have s2_update: "s2 = s2\<lparr>PTranscript := ?dg # rest\<rparr>"
      using alpha_res by simp
    show ?thesis
      by (subst s2_update[symmetric]) (rule read_dg)
  qed
  have dg_res:
    "dg = ?dg \<and>
     s3 = s2\<lparr>PState := concat (PState s2) ?dg, PTranscript := rest\<rparr>"
    using p.read_cons_outcome[OF read_dg_start] by simp
  have degree_ok: "to_nat dg \<le> p.maxDegree"
    using honest_degree_message_assert_hol[OF htv, of as] dg_res by simp
  have t_eq: "t = s3"
    using degree_assert degree_ok by (simp add: assert_def)
  have replay_s1: "replay_state \<le> s1"
    using read_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s2_s3: "s2 \<le> s3"
    using dg_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have replay_t: "replay_state \<le> t"
    using replay_s1 alpha_res s2_s3 unfolding t_eq by (meson p.hash_ext_trans)
  show ?thesis
    using read_res alpha_res dg_res t_eq replay_t by simp
qed

lemma honest_root_alpha_degree_fri_prefix_no_failure:
  assumes htv: "honest_trace_valid"
    and len_as: "length as = length spec"
    and len_challenges: "length challenges = length roots"
    and prefix:
      "PTranscript replay_state =
        value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @ roots @ rest"
    and alpha_lookups:
      "\<forall>i < length as.
        fmlookup (HashMap replay_state)
          (AlphaChallenge (PAlphaCounter replay_state + i)
            (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
          Some (as ! i)"
    and fri_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap replay_state)
          (FiatShamirChallenge (foldl concat
            (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
              (of_nat (degree (p.cp as p.f_powers))))
            (take (Suc i) roots))) =
          Some (challenges ! i)"
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
        fl \<leftarrow> ntimes v.receive_fri_commits (length roots);
        return (fr, as', dg, fl)
      }) replay_state))"
proof -
  let ?dg = "of_nat (degree (p.cp as p.f_powers))"
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  let ?prefix =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      return (fr, as', dg)
    }"
  let ?full =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      fl \<leftarrow> ntimes v.receive_fri_commits (length roots);
      return (fr, as', dg, fl)
    }"
  have prefix_nf:
    "None \<notin> dom (dist (execute ?prefix replay_state))"
  proof -
    have prefix_root_alpha_degree:
      "PTranscript replay_state =
        value f_merkle # as @ [?dg] @ (roots @ rest)"
      using prefix by simp
    show ?thesis
      by (rule honest_root_alpha_degree_prefix_no_failure[
          OF htv len_as prefix_root_alpha_degree alpha_lookups])
  qed
  have full_eq:
    "?full =
      (?prefix \<bind>
        (\<lambda>out.
          ntimes v.receive_fri_commits (length roots) \<bind>
            (\<lambda>fl. return (case out of (fr, as', dg) \<Rightarrow> (fr, as', dg, fl)))))"
    by (simp add: sm_bind_assoc split: prod.splits)
  show ?thesis
    unfolding full_eq
  proof (rule no_failure_bindI[OF prefix_nf])
    fix out s_prefix
    assume prefix_out:
      "Some (out, s_prefix) \<in> set_dist (execute ?prefix replay_state)"
    obtain fr as' dg where out_eq: "out = (fr, as', dg)"
      by (cases out)
    have prefix_out':
      "Some ((fr, as', dg), s_prefix) \<in> set_dist (execute ?prefix replay_state)"
      using prefix_out unfolding out_eq .
    have prefix_res:
      "fr = value f_merkle \<and>
       as' = as \<and>
       dg = ?dg \<and>
       PState s_prefix =
         concat (foldl concat (concat (PState replay_state) (value f_merkle)) as) ?dg \<and>
       PTranscript s_prefix = roots @ rest \<and>
       replay_state \<le> s_prefix"
    proof -
      have prefix_root_alpha_degree:
        "PTranscript replay_state =
          value f_merkle # as @ [?dg] @ (roots @ rest)"
        using prefix by simp
      show ?thesis
        by (rule honest_root_alpha_degree_prefix_outcome[
            OF htv len_as prefix_root_alpha_degree alpha_lookups prefix_out'])
    qed
    have fri_lookups_prefix:
      "\<forall>i < length roots.
        fmlookup (HashMap s_prefix)
          (FiatShamirChallenge (foldl concat (PState s_prefix) (take (Suc i) roots))) =
          Some (challenges ! i)"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < length roots"
      have lookup_replay:
        "fmlookup (HashMap replay_state)
          (FiatShamirChallenge (foldl concat
            (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
              ?dg)
            (take (Suc i) roots))) =
          Some (challenges ! i)"
        using fri_lookups i_bound by simp
      show "fmlookup (HashMap s_prefix)
        (FiatShamirChallenge (foldl concat (PState s_prefix) (take (Suc i) roots))) =
        Some (challenges ! i)"
        using p.hash_extension_lookup[OF lookup_replay, of s_prefix] prefix_res
        by simp
    qed
    have fri_nf_start:
      "None \<notin> dom (dist (execute
        (ntimes v.receive_fri_commits (length roots))
        (s_prefix\<lparr>PTranscript := roots @ rest\<rparr>)))"
      using honest_receive_fri_commits_list_no_failure[
        OF fri_lookups_prefix len_challenges, of rest] .
    have s_prefix_update: "s_prefix\<lparr>PTranscript := roots @ rest\<rparr> = s_prefix"
      using prefix_res by simp
    have fri_nf:
      "None \<notin> dom (dist (execute
        (ntimes v.receive_fri_commits (length roots)) s_prefix))"
      using fri_nf_start unfolding s_prefix_update .
    show "None \<notin> dom (dist (execute
      (ntimes v.receive_fri_commits (length roots) \<bind>
        (\<lambda>fl. return (case out of (fr, as', dg) \<Rightarrow> (fr, as', dg, fl))))
      s_prefix))"
      by (rule no_failure_bind_returnI[OF fri_nf])
  qed
qed

lemma honest_root_alpha_degree_fri_final_prefix_no_failure:
  assumes htv: "honest_trace_valid"
    and len_as: "length as = length spec"
    and len_challenges: "length challenges = length roots"
    and prefix:
      "PTranscript replay_state =
        value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
          roots @ [final_msg] @ rest"
    and alpha_lookups:
      "\<forall>i < length as.
        fmlookup (HashMap replay_state)
          (AlphaChallenge (PAlphaCounter replay_state + i)
            (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
          Some (as ! i)"
    and fri_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap replay_state)
          (FiatShamirChallenge (foldl concat
            (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
              (of_nat (degree (p.cp as p.f_powers))))
            (take (Suc i) roots))) =
          Some (challenges ! i)"
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
        fl \<leftarrow> ntimes v.receive_fri_commits (length roots);
        final \<leftarrow> p.read;
        return (fr, as', dg, fl, final)
      }) replay_state))"
proof -
  let ?dg = "of_nat (degree (p.cp as p.f_powers))"
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  let ?prefix =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      return (fr, as', dg)
    }"
  let ?rad_fri =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      fl \<leftarrow> ntimes v.receive_fri_commits (length roots);
      return (fr, as', dg, fl)
    }"
  have prefix_nf:
    "None \<notin> dom (dist (execute ?rad_fri replay_state))"
  proof -
    have prefix': "PTranscript replay_state =
      value f_merkle # as @ [?dg] @ roots @ ([final_msg] @ rest)"
      using prefix by simp
    show ?thesis
      by (rule honest_root_alpha_degree_fri_prefix_no_failure[
          OF htv len_as len_challenges prefix' alpha_lookups fri_lookups])
  qed
  have full_eq:
    "(do {
        fr \<leftarrow> p.read;
        as' \<leftarrow> mmap (replicate (length spec) ?round);
        dg \<leftarrow> p.read;
        assert (to_nat dg \<le> p.maxDegree);
        fl \<leftarrow> ntimes v.receive_fri_commits (length roots);
        final \<leftarrow> p.read;
        return (fr, as', dg, fl, final)
      }) =
      (?rad_fri \<bind>
        (\<lambda>out. p.read \<bind>
          (\<lambda>final. return (case out of (fr, as', dg, fl) \<Rightarrow>
            (fr, as', dg, fl, final)))))"
    by (simp add: sm_bind_assoc split: prod.splits)
  show ?thesis
    unfolding full_eq
  proof (rule no_failure_bindI[OF prefix_nf])
    fix out s_fri
    assume prefix_out:
      "Some (out, s_fri) \<in> set_dist (execute ?rad_fri replay_state)"
    obtain fr as' dg fl where out_eq: "out = (fr, as', dg, fl)"
      by (cases out) auto
    from prefix_out[unfolded out_eq] obtain s1 s2 s3 s_prefix where
      read_fr: "Some (fr, s1) \<in> set_dist (execute p.read replay_state)"
      and alpha_out:
        "Some (as', s2) \<in>
          set_dist (execute (mmap (replicate (length spec) ?round)) s1)"
      and read_dg: "Some (dg, s3) \<in> set_dist (execute p.read s2)"
      and degree_assert:
        "Some ((), s_prefix) \<in>
          set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s3)"
      and fri_out:
        "Some (fl, s_fri) \<in>
          set_dist (execute (ntimes v.receive_fri_commits (length roots)) s_prefix)"
      by (auto elim!: p.set_dist_bindE split: prod.splits)
    have prefix3_out:
      "Some ((fr, as', dg), s_prefix) \<in> set_dist (execute ?prefix replay_state)"
      apply (rule set_dist_bindI[OF read_fr])
      apply (rule set_dist_bindI[OF alpha_out])
      apply (rule set_dist_bindI[OF read_dg])
      apply (rule set_dist_bindI[OF degree_assert])
      by simp
    have prefix3:
      "PTranscript replay_state =
        value f_merkle # as @ [?dg] @ (roots @ [final_msg] @ rest)"
      using prefix by simp
    have prefix_res:
      "fr = value f_merkle \<and>
       as' = as \<and>
       dg = ?dg \<and>
       PState s_prefix =
         concat (foldl concat (concat (PState replay_state) (value f_merkle)) as) ?dg \<and>
       PTranscript s_prefix = roots @ [final_msg] @ rest \<and>
       replay_state \<le> s_prefix"
      by (rule honest_root_alpha_degree_prefix_outcome[
          OF htv len_as prefix3 alpha_lookups prefix3_out])
    have fri_lookups_prefix:
      "\<forall>i < length roots.
        fmlookup (HashMap s_prefix)
          (FiatShamirChallenge (foldl concat (PState s_prefix) (take (Suc i) roots))) =
          Some (challenges ! i)"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < length roots"
      have lookup_replay:
        "fmlookup (HashMap replay_state)
          (FiatShamirChallenge (foldl concat
            (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
              ?dg)
            (take (Suc i) roots))) =
          Some (challenges ! i)"
        using fri_lookups i_bound by simp
      show "fmlookup (HashMap s_prefix)
        (FiatShamirChallenge (foldl concat (PState s_prefix) (take (Suc i) roots))) =
        Some (challenges ! i)"
        using p.hash_extension_lookup[OF lookup_replay, of s_prefix] prefix_res
        by simp
    qed
    have fri_out':
      "Some (fl, s_fri) \<in>
        set_dist (execute (ntimes v.receive_fri_commits (length roots))
          (s_prefix\<lparr>PTranscript := roots @ ([final_msg] @ rest)\<rparr>))"
    proof -
      have "s_prefix\<lparr>PTranscript := roots @ ([final_msg] @ rest)\<rparr> = s_prefix"
        using prefix_res by (cases s_prefix) simp
      then show ?thesis
        using fri_out by simp
    qed
    have tr_fri: "PTranscript s_fri = final_msg # rest"
      using honest_receive_fri_commits_list_outcome[
        OF fri_lookups_prefix len_challenges fri_out']
      by simp
    show "None \<notin> dom (dist (execute
      (p.read \<bind>
        (\<lambda>final. return (case out of (fr, as', dg, fl) \<Rightarrow>
          (fr, as', dg, fl, final)))) s_fri))"
      unfolding out_eq
      by (rule no_failure_bind_returnI)
        (rule p.read_no_failure, simp add: tr_fri)
  qed
qed

lemma honest_root_alpha_degree_fri_final_prefix_outcome:
  assumes htv: "honest_trace_valid"
    and len_as: "length as = length spec"
    and len_challenges: "length challenges = length roots"
    and prefix:
      "PTranscript replay_state =
        value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
          roots @ [final_msg] @ rest"
    and alpha_lookups:
      "\<forall>i < length as.
        fmlookup (HashMap replay_state)
          (AlphaChallenge (PAlphaCounter replay_state + i)
            (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
          Some (as ! i)"
    and fri_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap replay_state)
          (FiatShamirChallenge (foldl concat
            (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
              (of_nat (degree (p.cp as p.f_powers))))
            (take (Suc i) roots))) =
          Some (challenges ! i)"
    and outcome:
      "Some ((fr, as', dg, fl, final), t) \<in> set_dist (execute
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
          fl \<leftarrow> ntimes v.receive_fri_commits (length roots);
          final \<leftarrow> p.read;
          return (fr, as', dg, fl, final)
        }) replay_state)"
  shows
    "fr = value f_merkle \<and>
     as' = as \<and>
     dg = of_nat (degree (p.cp as p.f_powers)) \<and>
     fl = zip challenges roots \<and>
     final = final_msg \<and>
     PState t =
       concat
         (foldl concat
           (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
             (of_nat (degree (p.cp as p.f_powers))))
           roots)
         final_msg \<and>
     PTranscript t = rest \<and>
     replay_state \<le> t"
proof -
  let ?dg = "of_nat (degree (p.cp as p.f_powers))"
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  let ?rad =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      return (fr, as', dg)
    }"
  from outcome obtain s1 s2 s3 s_prefix s_fri where
    read_fr: "Some (fr, s1) \<in> set_dist (execute p.read replay_state)"
    and alpha_out:
      "Some (as', s2) \<in>
        set_dist (execute (mmap (replicate (length spec) ?round)) s1)"
    and read_dg: "Some (dg, s3) \<in> set_dist (execute p.read s2)"
    and degree_assert:
      "Some ((), s_prefix) \<in>
        set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s3)"
    and fri_out:
      "Some (fl, s_fri) \<in>
        set_dist (execute (ntimes v.receive_fri_commits (length roots)) s_prefix)"
    and read_final:
      "Some (final, t) \<in> set_dist (execute p.read s_fri)"
    by (auto elim!: p.set_dist_bindE)
  have rad_out:
    "Some ((fr, as', dg), s_prefix) \<in> set_dist (execute ?rad replay_state)"
    apply (rule set_dist_bindI[OF read_fr])
    apply (rule set_dist_bindI[OF alpha_out])
    apply (rule set_dist_bindI[OF read_dg])
    apply (rule set_dist_bindI[OF degree_assert])
    by simp
  have rad_prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [?dg] @ (roots @ [final_msg] @ rest)"
    using prefix by simp
  have rad_res:
    "fr = value f_merkle \<and>
     as' = as \<and>
     dg = ?dg \<and>
     PState s_prefix =
       concat (foldl concat (concat (PState replay_state) (value f_merkle)) as) ?dg \<and>
     PTranscript s_prefix = roots @ [final_msg] @ rest \<and>
     replay_state \<le> s_prefix"
    by (rule honest_root_alpha_degree_prefix_outcome[
        OF htv len_as rad_prefix alpha_lookups rad_out])
  have fri_lookups_prefix:
    "\<forall>i < length roots.
      fmlookup (HashMap s_prefix)
        (FiatShamirChallenge (foldl concat (PState s_prefix) (take (Suc i) roots))) =
        Some (challenges ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length roots"
    have lookup_replay:
      "fmlookup (HashMap replay_state)
        (FiatShamirChallenge (foldl concat
          (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
            ?dg)
          (take (Suc i) roots))) =
        Some (challenges ! i)"
      using fri_lookups i_bound by simp
    show "fmlookup (HashMap s_prefix)
      (FiatShamirChallenge (foldl concat (PState s_prefix) (take (Suc i) roots))) =
      Some (challenges ! i)"
      using p.hash_extension_lookup[OF lookup_replay, of s_prefix] rad_res
      by simp
  qed
  have s_prefix_update:
    "s_prefix\<lparr>PTranscript := roots @ [final_msg] @ rest\<rparr> = s_prefix"
    using rad_res by simp
  have fri_out':
    "Some (fl, s_fri) \<in>
      set_dist (execute (ntimes v.receive_fri_commits (length roots))
        (s_prefix\<lparr>PTranscript := roots @ ([final_msg] @ rest)\<rparr>))"
    using fri_out unfolding s_prefix_update by simp
  have fri_res:
    "fl = zip challenges roots \<and>
     PState s_fri = foldl concat (PState s_prefix) roots \<and>
     PTranscript s_fri = [final_msg] @ rest \<and>
     s_prefix \<le> s_fri"
    using honest_receive_fri_commits_list_outcome[
      OF fri_lookups_prefix len_challenges fri_out'] .
  have read_final':
    "Some (final, t) \<in>
      set_dist (execute p.read (s_fri\<lparr>PTranscript := final_msg # rest\<rparr>))"
  proof -
    have update: "s_fri = s_fri\<lparr>PTranscript := final_msg # rest\<rparr>"
      using fri_res by simp
    show ?thesis
      by (subst update[symmetric]) (rule read_final)
  qed
  have final_res:
    "final = final_msg \<and>
     t = s_fri\<lparr>PState := concat (PState s_fri) final_msg, PTranscript := rest\<rparr>"
    using p.read_cons_outcome[OF read_final'] by simp
  have replay_t: "replay_state \<le> t"
  proof -
    have s_fri_t: "s_fri \<le> t"
      using final_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    show ?thesis
      using rad_res fri_res s_fri_t by (meson p.hash_ext_trans)
  qed
  show ?thesis
    using rad_res fri_res final_res replay_t by simp
qed

lemma honest_root_alpha_degree_fri_final_dynamic_prefix_outcome:
  assumes htv: "honest_trace_valid"
    and len_as: "length as = length spec"
    and len_challenges: "length challenges = length roots"
    and roots_rounds:
      "length roots = ceil_log (degree (p.cp as p.f_powers) + 1)"
    and prefix:
      "PTranscript replay_state =
        value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
          roots @ [final_msg] @ rest"
    and alpha_lookups:
      "\<forall>i < length as.
        fmlookup (HashMap replay_state)
          (AlphaChallenge (PAlphaCounter replay_state + i)
            (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
          Some (as ! i)"
    and fri_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap replay_state)
          (FiatShamirChallenge (foldl concat
            (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
              (of_nat (degree (p.cp as p.f_powers))))
            (take (Suc i) roots))) =
          Some (challenges ! i)"
    and outcome:
      "Some ((fr, as', dg, fl, final), t) \<in> set_dist (execute
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
          return (fr, as', dg, fl, final)
        }) replay_state)"
  shows
    "fr = value f_merkle \<and>
     as' = as \<and>
     dg = of_nat (degree (p.cp as p.f_powers)) \<and>
     fl = zip challenges roots \<and>
     final = final_msg \<and>
     PState t =
       concat
         (foldl concat
           (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
             (of_nat (degree (p.cp as p.f_powers))))
           roots)
         final_msg \<and>
     PTranscript t = rest \<and>
     replay_state \<le> t"
proof -
  let ?dg = "of_nat (degree (p.cp as p.f_powers))"
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  let ?rad =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      return (fr, as', dg)
    }"
  from outcome obtain s1 s2 s3 s_prefix s_fri where
    read_fr: "Some (fr, s1) \<in> set_dist (execute p.read replay_state)"
    and alpha_out:
      "Some (as', s2) \<in>
        set_dist (execute (mmap (replicate (length spec) ?round)) s1)"
    and read_dg: "Some (dg, s3) \<in> set_dist (execute p.read s2)"
    and degree_assert:
      "Some ((), s_prefix) \<in>
        set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s3)"
    and fri_out:
      "Some (fl, s_fri) \<in>
        set_dist (execute (ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1))) s_prefix)"
    and read_final:
      "Some (final, t) \<in> set_dist (execute p.read s_fri)"
    by (auto elim!: p.set_dist_bindE)
  have rad_out:
    "Some ((fr, as', dg), s_prefix) \<in> set_dist (execute ?rad replay_state)"
    apply (rule set_dist_bindI[OF read_fr])
    apply (rule set_dist_bindI[OF alpha_out])
    apply (rule set_dist_bindI[OF read_dg])
    apply (rule set_dist_bindI[OF degree_assert])
    by simp
  have rad_prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [?dg] @ (roots @ [final_msg] @ rest)"
    using prefix by simp
  have rad_res:
    "fr = value f_merkle \<and>
     as' = as \<and>
     dg = ?dg \<and>
     PState s_prefix =
       concat (foldl concat (concat (PState replay_state) (value f_merkle)) as) ?dg \<and>
     PTranscript s_prefix = roots @ [final_msg] @ rest \<and>
     replay_state \<le> s_prefix"
    by (rule honest_root_alpha_degree_prefix_outcome[
        OF htv len_as rad_prefix alpha_lookups rad_out])
  have rounds_eq: "ceil_log (to_nat dg + 1) = length roots"
    using honest_degree_message_rounds[OF htv, of as] rad_res roots_rounds by simp
  have fri_lookups_prefix:
    "\<forall>i < length roots.
      fmlookup (HashMap s_prefix)
        (FiatShamirChallenge (foldl concat (PState s_prefix) (take (Suc i) roots))) =
        Some (challenges ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length roots"
    have lookup_replay:
      "fmlookup (HashMap replay_state)
        (FiatShamirChallenge (foldl concat
          (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
            ?dg)
          (take (Suc i) roots))) =
        Some (challenges ! i)"
      using fri_lookups i_bound by simp
    show "fmlookup (HashMap s_prefix)
      (FiatShamirChallenge (foldl concat (PState s_prefix) (take (Suc i) roots))) =
      Some (challenges ! i)"
      using p.hash_extension_lookup[OF lookup_replay, of s_prefix] rad_res
      by simp
  qed
  have s_prefix_update:
    "s_prefix\<lparr>PTranscript := roots @ [final_msg] @ rest\<rparr> = s_prefix"
    using rad_res by simp
  have fri_out':
    "Some (fl, s_fri) \<in>
      set_dist (execute (ntimes v.receive_fri_commits (length roots))
        (s_prefix\<lparr>PTranscript := roots @ ([final_msg] @ rest)\<rparr>))"
    using fri_out rounds_eq unfolding s_prefix_update by simp
  have fri_res:
    "fl = zip challenges roots \<and>
     PState s_fri = foldl concat (PState s_prefix) roots \<and>
     PTranscript s_fri = [final_msg] @ rest \<and>
     s_prefix \<le> s_fri"
    using honest_receive_fri_commits_list_outcome[
      OF fri_lookups_prefix len_challenges fri_out'] .
  have read_final':
    "Some (final, t) \<in>
      set_dist (execute p.read (s_fri\<lparr>PTranscript := final_msg # rest\<rparr>))"
  proof -
    have update: "s_fri = s_fri\<lparr>PTranscript := final_msg # rest\<rparr>"
      using fri_res by simp
    show ?thesis
      by (subst update[symmetric]) (rule read_final)
  qed
  have final_res:
    "final = final_msg \<and>
     t = s_fri\<lparr>PState := concat (PState s_fri) final_msg, PTranscript := rest\<rparr>"
    using p.read_cons_outcome[OF read_final'] by simp
  have replay_t: "replay_state \<le> t"
  proof -
    have s_fri_t: "s_fri \<le> t"
      using final_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    show ?thesis
      using rad_res fri_res s_fri_t by (meson p.hash_ext_trans)
  qed
	  show ?thesis
	    using rad_res fri_res final_res replay_t by simp
	qed

lemma honest_root_alpha_degree_fri_final_prefix_preserves_query_counter:
  assumes outcome:
    "Some ((fr, as', dg, fl, final), t) \<in> set_dist (execute
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
        fl \<leftarrow> ntimes v.receive_fri_commits n;
        final \<leftarrow> p.read;
        return (fr, as', dg, fl, final)
      }) s)"
  shows "PQueryCounter t = PQueryCounter s"
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
  from outcome obtain s_read s_alpha s_dg s_assert s_fri where
    read_fr: "Some (fr, s_read) \<in> set_dist (execute p.read s)"
    and alpha_out:
      "Some (as', s_alpha) \<in>
        set_dist (execute (mmap (replicate (length spec) ?round)) s_read)"
    and read_dg: "Some (dg, s_dg) \<in> set_dist (execute p.read s_alpha)"
    and assert_dg:
      "Some ((), s_assert) \<in>
        set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s_dg)"
    and fri_out:
      "Some (fl, s_fri) \<in>
        set_dist (execute (ntimes v.receive_fri_commits n) s_assert)"
    and read_final: "Some (final, t) \<in> set_dist (execute p.read s_fri)"
    by (auto elim!: p.set_dist_bindE)
  have q_read: "PQueryCounter s_read = PQueryCounter s"
    using read_preserves_counters[OF read_fr] by simp
  have q_alpha: "PQueryCounter s_alpha = PQueryCounter s_read"
    by (rule honest_alpha_mmap_replay_preserves_query_counter[OF alpha_out])
  have q_dg: "PQueryCounter s_dg = PQueryCounter s_alpha"
    using read_preserves_counters[OF read_dg] by simp
  have s_assert_eq: "s_assert = s_dg"
    using assert_outcomeD(2)[OF assert_dg] .
  have q_fri: "PQueryCounter s_fri = PQueryCounter s_assert"
    by (rule receive_fri_commits_preserves_query_counter[OF fri_out])
  have q_final: "PQueryCounter t = PQueryCounter s_fri"
    using read_preserves_counters[OF read_final] by simp
  show ?thesis
    using q_read q_alpha q_dg q_fri q_final unfolding s_assert_eq by simp
qed

lemma honest_root_alpha_degree_fri_final_dynamic_prefix_preserves_query_counter:
  assumes outcome:
    "Some ((fr, as', dg, fl, final), t) \<in> set_dist (execute
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
        return (fr, as', dg, fl, final)
      }) s)"
  shows "PQueryCounter t = PQueryCounter s"
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
  from outcome obtain s_read s_alpha s_dg s_assert s_fri where
    read_fr: "Some (fr, s_read) \<in> set_dist (execute p.read s)"
    and alpha_out:
      "Some (as', s_alpha) \<in>
        set_dist (execute (mmap (replicate (length spec) ?round)) s_read)"
    and read_dg: "Some (dg, s_dg) \<in> set_dist (execute p.read s_alpha)"
    and assert_dg:
      "Some ((), s_assert) \<in>
        set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s_dg)"
    and fri_out:
      "Some (fl, s_fri) \<in>
        set_dist (execute (ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1))) s_assert)"
    and read_final: "Some (final, t) \<in> set_dist (execute p.read s_fri)"
    by (auto elim!: p.set_dist_bindE)
  have q_read: "PQueryCounter s_read = PQueryCounter s"
    using read_preserves_counters[OF read_fr] by simp
  have q_alpha: "PQueryCounter s_alpha = PQueryCounter s_read"
    by (rule honest_alpha_mmap_replay_preserves_query_counter[OF alpha_out])
  have q_dg: "PQueryCounter s_dg = PQueryCounter s_alpha"
    using read_preserves_counters[OF read_dg] by simp
  have s_assert_eq: "s_assert = s_dg"
    using assert_outcomeD(2)[OF assert_dg] .
  have q_fri: "PQueryCounter s_fri = PQueryCounter s_assert"
    by (rule receive_fri_commits_preserves_query_counter[OF fri_out])
  have q_final: "PQueryCounter t = PQueryCounter s_fri"
    using read_preserves_counters[OF read_final] by simp
  show ?thesis
    using q_read q_alpha q_dg q_fri q_final unfolding s_assert_eq by simp
qed

lemma honest_root_alpha_degree_fri_final_dynamic_prefix_no_failure:
  assumes htv: "honest_trace_valid"
    and len_as: "length as = length spec"
    and len_challenges: "length challenges = length roots"
    and roots_rounds:
      "length roots = ceil_log (degree (p.cp as p.f_powers) + 1)"
    and prefix:
      "PTranscript replay_state =
        value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
          roots @ [final_msg] @ rest"
    and alpha_lookups:
      "\<forall>i < length as.
        fmlookup (HashMap replay_state)
          (AlphaChallenge (PAlphaCounter replay_state + i)
            (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
          Some (as ! i)"
    and fri_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap replay_state)
          (FiatShamirChallenge (foldl concat
            (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
              (of_nat (degree (p.cp as p.f_powers))))
            (take (Suc i) roots))) =
          Some (challenges ! i)"
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
        return (fr, as', dg, fl, final)
      }) replay_state))"
proof -
  let ?dg = "of_nat (degree (p.cp as p.f_powers))"
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  let ?rad =
    "do {
      fr \<leftarrow> p.read;
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      return (fr, as', dg)
    }"
  have rad_prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [?dg] @ (roots @ [final_msg] @ rest)"
    using prefix by simp
  have rad_nf:
    "None \<notin> dom (dist (execute ?rad replay_state))"
    by (rule honest_root_alpha_degree_prefix_no_failure[
        OF htv len_as rad_prefix alpha_lookups])
  have full_eq:
    "(do {
        fr \<leftarrow> p.read;
        as' \<leftarrow> mmap (replicate (length spec) ?round);
        dg \<leftarrow> p.read;
        assert (to_nat dg \<le> p.maxDegree);
        fl \<leftarrow> ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1));
        final \<leftarrow> p.read;
        return (fr, as', dg, fl, final)
      }) =
      (?rad \<bind>
        (\<lambda>out. case out of (fr, as', dg) \<Rightarrow>
          ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1)) \<bind>
          (\<lambda>fl. p.read \<bind>
          (\<lambda>final. return (fr, as', dg, fl, final)))))"
    by (simp add: sm_bind_assoc split: prod.splits)
  show ?thesis
    unfolding full_eq
  proof (rule no_failure_bindI[OF rad_nf])
    fix out s_prefix
    assume rad_out: "Some (out, s_prefix) \<in> set_dist (execute ?rad replay_state)"
    obtain fr as' dg where out_eq: "out = (fr, as', dg)"
      by (cases out) auto
    have rad_out':
      "Some ((fr, as', dg), s_prefix) \<in> set_dist (execute ?rad replay_state)"
      using rad_out unfolding out_eq .
    have rad_res:
      "fr = value f_merkle \<and>
       as' = as \<and>
       dg = ?dg \<and>
       PState s_prefix =
         concat (foldl concat (concat (PState replay_state) (value f_merkle)) as) ?dg \<and>
       PTranscript s_prefix = roots @ [final_msg] @ rest \<and>
       replay_state \<le> s_prefix"
      by (rule honest_root_alpha_degree_prefix_outcome[
          OF htv len_as rad_prefix alpha_lookups rad_out'])
    have rounds_eq: "ceil_log (to_nat dg + 1) = length roots"
      using honest_degree_message_rounds[OF htv, of as] rad_res roots_rounds by simp
    have fri_lookups_prefix:
      "\<forall>i < length roots.
        fmlookup (HashMap s_prefix)
          (FiatShamirChallenge (foldl concat (PState s_prefix) (take (Suc i) roots))) =
          Some (challenges ! i)"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < length roots"
      have lookup_replay:
        "fmlookup (HashMap replay_state)
          (FiatShamirChallenge (foldl concat
            (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
              ?dg)
            (take (Suc i) roots))) =
          Some (challenges ! i)"
        using fri_lookups i_bound by simp
      show "fmlookup (HashMap s_prefix)
        (FiatShamirChallenge (foldl concat (PState s_prefix) (take (Suc i) roots))) =
        Some (challenges ! i)"
        using p.hash_extension_lookup[OF lookup_replay, of s_prefix] rad_res
        by simp
    qed
    have s_prefix_update:
      "s_prefix\<lparr>PTranscript := roots @ [final_msg] @ rest\<rparr> = s_prefix"
      using rad_res by simp
    have fri_nf_start:
      "None \<notin> dom (dist (execute
        (ntimes v.receive_fri_commits (length roots))
        (s_prefix\<lparr>PTranscript := roots @ ([final_msg] @ rest)\<rparr>)))"
      using honest_receive_fri_commits_list_no_failure[
        OF fri_lookups_prefix len_challenges, of "[final_msg] @ rest"] .
	    have fri_nf:
	      "None \<notin> dom (dist (execute
	        (ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1))) s_prefix))"
	      using fri_nf_start unfolding rounds_eq s_prefix_update by simp
    have cont_nf:
      "None \<notin> dom (dist (execute
        (ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1)) \<bind>
          (\<lambda>fl. p.read \<bind> (\<lambda>final. return (fr, as', dg, fl, final)))) s_prefix))"
    proof (rule no_failure_bindI[OF fri_nf])
      fix fl t
      assume fri_out:
        "Some (fl, t) \<in>
          set_dist (execute
            (ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1))) s_prefix)"
      have fri_out_start:
        "Some (fl, t) \<in>
          set_dist (execute
            (ntimes v.receive_fri_commits (length roots))
            (s_prefix\<lparr>PTranscript := roots @ ([final_msg] @ rest)\<rparr>))"
        using fri_out unfolding rounds_eq s_prefix_update by simp
      have tr_t: "PTranscript t = final_msg # rest"
        using honest_receive_fri_commits_list_outcome[
          OF fri_lookups_prefix len_challenges fri_out_start]
        by simp
      show "None \<notin> dom
        (dist (execute (p.read \<bind>
          (\<lambda>final. return (fr, as', dg, fl, final))) t))"
        by (rule no_failure_bind_returnI)
          (rule p.read_no_failure, simp add: tr_t)
    qed
	    show "None \<notin> dom (dist (execute
	      ((case out of (fr, as', dg) \<Rightarrow>
	        ntimes v.receive_fri_commits (ceil_log (to_nat dg + 1)) \<bind>
	        (\<lambda>fl. p.read \<bind> (\<lambda>final. return (fr, as', dg, fl, final))))) s_prefix))"
	      unfolding out_eq
      using cont_nf by simp
	  qed
	qed

lemma honest_alpha_degree_fri_final_dynamic_prefix_outcome:
  assumes htv: "honest_trace_valid"
    and len_as: "length as = length spec"
    and len_challenges: "length challenges = length roots"
    and roots_rounds:
      "length roots = ceil_log (degree (p.cp as p.f_powers) + 1)"
    and prefix:
      "PTranscript replay_state =
        as @ [of_nat (degree (p.cp as p.f_powers))] @ roots @ [final_msg] @ rest"
    and alpha_lookups:
      "\<forall>i < length as.
        fmlookup (HashMap replay_state)
          (AlphaChallenge (PAlphaCounter replay_state + i)
            (foldl concat (PState replay_state) (take i as))) =
          Some (as ! i)"
    and fri_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap replay_state)
          (CompositionFriChallenge (PCompositionFriCounter replay_state + i) (foldl concat
            (concat (foldl concat (PState replay_state) as)
              (of_nat (degree (p.cp as p.f_powers))))
            (take (Suc i) roots))) =
          Some (challenges ! i)"
    and outcome:
      "Some ((as', dg, fl, final), t) \<in> set_dist (execute
        (do {
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
          fl \<leftarrow> ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1));
          final \<leftarrow> p.read;
          return (as', dg, fl, final)
        }) replay_state)"
  shows
    "as' = as \<and>
     dg = of_nat (degree (p.cp as p.f_powers)) \<and>
     fl = zip challenges roots \<and>
     final = final_msg \<and>
     PState t =
       concat
         (foldl concat
           (concat (foldl concat (PState replay_state) as)
             (of_nat (degree (p.cp as p.f_powers))))
           roots)
         final_msg \<and>
     PTranscript t = rest \<and>
     replay_state \<le> t"
proof -
  let ?dg = "of_nat (degree (p.cp as p.f_powers))"
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  let ?ad =
    "do {
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      return (as', dg)
    }"
  from outcome obtain s_alpha s_dg s_prefix s_fri where
    alpha_out:
      "Some (as', s_alpha) \<in>
        set_dist (execute (mmap (replicate (length spec) ?round)) replay_state)"
    and read_dg: "Some (dg, s_dg) \<in> set_dist (execute p.read s_alpha)"
    and degree_assert:
      "Some ((), s_prefix) \<in>
        set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s_dg)"
    and fri_out:
      "Some (fl, s_fri) \<in>
        set_dist (execute
          (ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1)))
          s_prefix)"
    and read_final:
      "Some (final, t) \<in> set_dist (execute p.read s_fri)"
    by (auto elim!: p.set_dist_bindE)
  have alpha_start:
    "Some (as', s_alpha) \<in>
      set_dist (execute (mmap (replicate (length as) ?round))
        (replay_state\<lparr>PTranscript := as @ [?dg] @ roots @ [final_msg] @ rest\<rparr>))"
  proof -
    have alpha_out_as:
      "Some (as', s_alpha) \<in>
        set_dist (execute (mmap (replicate (length as) ?round)) replay_state)"
      using alpha_out len_as by simp
    have replay_update:
      "replay_state =
        replay_state\<lparr>PTranscript := as @ [?dg] @ roots @ [final_msg] @ rest\<rparr>"
      using prefix by (simp add: append_assoc)
    show ?thesis
      by (subst replay_update[symmetric]) (rule alpha_out_as)
  qed
  have alpha_res:
    "as' = as \<and>
     PState s_alpha = foldl concat (PState replay_state) as \<and>
     PTranscript s_alpha = ?dg # roots @ [final_msg] @ rest \<and>
     PCompositionFriCounter s_alpha = PCompositionFriCounter replay_state \<and>
     replay_state \<le> s_alpha"
    using honest_alpha_mmap_replay_outcome[OF alpha_lookups alpha_start] by simp
  have read_dg':
    "Some (dg, s_dg) \<in>
      set_dist (execute p.read (s_alpha\<lparr>PTranscript := ?dg # roots @ [final_msg] @ rest\<rparr>))"
  proof -
    have s_alpha_update:
      "s_alpha = s_alpha\<lparr>PTranscript := ?dg # roots @ [final_msg] @ rest\<rparr>"
      using alpha_res by simp
    then show ?thesis
      by (subst s_alpha_update[symmetric]) (rule read_dg)
  qed
  have dg_res:
    "dg = ?dg \<and>
     s_dg = s_alpha\<lparr>PState := concat (PState s_alpha) ?dg,
       PTranscript := roots @ [final_msg] @ rest\<rparr>"
    using p.read_cons_outcome[OF read_dg'] by simp
  have degree_ok: "to_nat dg \<le> p.maxDegree"
    using honest_degree_message_assert_hol[OF htv, of as] dg_res by simp
  have prefix_eq: "s_prefix = s_dg"
    using degree_assert degree_ok by (simp add: assert_def)
  have rounds_eq: "ceil_log (to_nat dg + 1) = length roots"
    using honest_degree_message_rounds[OF htv, of as] dg_res roots_rounds by simp
  have fri_lookups_prefix:
    "\<forall>i < length roots.
      fmlookup (HashMap s_prefix)
        (CompositionFriChallenge
          (PCompositionFriCounter s_prefix + i)
          (foldl concat (PState s_prefix) (take (Suc i) roots))) =
        Some (challenges ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length roots"
    have lookup_replay:
      "fmlookup (HashMap replay_state)
      (CompositionFriChallenge (PCompositionFriCounter replay_state + i) (foldl concat
        (concat (foldl concat (PState replay_state) as) ?dg)
        (take (Suc i) roots))) =
        Some (challenges ! i)"
      using fri_lookups i_bound by simp
    have lookup_alpha:
      "fmlookup (HashMap s_alpha)
        (CompositionFriChallenge (PCompositionFriCounter s_alpha + i) (foldl concat
          (concat (foldl concat (PState replay_state) as) ?dg)
          (take (Suc i) roots))) =
      Some (challenges ! i)"
      using p.hash_extension_lookup[OF lookup_replay, of s_alpha] alpha_res by simp
      show "fmlookup (HashMap s_prefix)
          (CompositionFriChallenge
            (PCompositionFriCounter s_prefix + i)
            (foldl concat (PState s_prefix) (take (Suc i) roots))) =
        Some (challenges ! i)"
      using lookup_alpha alpha_res dg_res prefix_eq by simp
  qed
  have fri_out':
      "Some (fl, s_fri) \<in>
      set_dist (execute (ntimes v.receive_composition_fri_commits (length roots))
        (s_prefix\<lparr>PTranscript := roots @ ([final_msg] @ rest)\<rparr>))"
    using fri_out rounds_eq alpha_res dg_res prefix_eq by simp
  have fri_res:
    "fl = zip challenges roots \<and>
     PState s_fri = foldl concat (PState s_prefix) roots \<and>
     PTranscript s_fri = [final_msg] @ rest \<and>
     s_prefix \<le> s_fri"
    using honest_receive_composition_fri_commits_list_outcome[
      OF fri_lookups_prefix len_challenges fri_out'] .
  have read_final':
    "Some (final, t) \<in>
      set_dist (execute p.read (s_fri\<lparr>PTranscript := final_msg # rest\<rparr>))"
  proof -
    have s_fri_update: "s_fri = s_fri\<lparr>PTranscript := final_msg # rest\<rparr>"
      using fri_res by simp
    then show ?thesis
      by (subst s_fri_update[symmetric]) (rule read_final)
  qed
  have final_res:
    "final = final_msg \<and>
     t = s_fri\<lparr>PState := concat (PState s_fri) final_msg, PTranscript := rest\<rparr>"
    using p.read_cons_outcome[OF read_final'] by simp
  have replay_t: "replay_state \<le> t"
  proof -
    have s_alpha_s_dg: "s_alpha \<le> s_dg"
      using dg_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    have s_fri_t: "s_fri \<le> t"
      using final_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    show ?thesis
      using alpha_res s_alpha_s_dg prefix_eq fri_res s_fri_t by (meson p.hash_ext_trans)
  qed
  show ?thesis
    using alpha_res dg_res prefix_eq fri_res final_res replay_t by simp
qed

lemma honest_alpha_degree_fri_final_dynamic_prefix_no_failure:
  assumes htv: "honest_trace_valid"
    and len_as: "length as = length spec"
    and len_challenges: "length challenges = length roots"
    and roots_rounds:
      "length roots = ceil_log (degree (p.cp as p.f_powers) + 1)"
    and prefix:
      "PTranscript replay_state =
        as @ [of_nat (degree (p.cp as p.f_powers))] @ roots @ [final_msg] @ rest"
    and alpha_lookups:
      "\<forall>i < length as.
        fmlookup (HashMap replay_state)
          (AlphaChallenge (PAlphaCounter replay_state + i)
            (foldl concat (PState replay_state) (take i as))) =
          Some (as ! i)"
    and fri_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap replay_state)
          (CompositionFriChallenge (PCompositionFriCounter replay_state + i) (foldl concat
            (concat (foldl concat (PState replay_state) as)
              (of_nat (degree (p.cp as p.f_powers))))
            (take (Suc i) roots))) =
          Some (challenges ! i)"
  shows
    "None \<notin> dom (dist (execute
      (do {
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
        fl \<leftarrow> ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1));
        final \<leftarrow> p.read;
        return (as', dg, fl, final)
      }) replay_state))"
proof -
  let ?dg = "of_nat (degree (p.cp as p.f_powers))"
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  let ?ad =
    "do {
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      return (as', dg)
    }"
  have alpha_nf_start:
    "None \<notin> dom (dist (execute
      (mmap (replicate (length as) ?round))
      (replay_state\<lparr>PTranscript := as @ [?dg] @ roots @ [final_msg] @ rest\<rparr>)))"
    using honest_alpha_mmap_replay_no_failure[OF alpha_lookups, of "?dg # roots @ [final_msg] @ rest"]
    by (simp add: append_assoc)
  have alpha_nf:
    "None \<notin> dom (dist (execute
      (mmap (replicate (length spec) ?round)) replay_state))"
  proof -
    have replay_update:
      "replay_state =
        replay_state\<lparr>PTranscript := as @ [?dg] @ roots @ [final_msg] @ rest\<rparr>"
      using prefix by (simp add: append_assoc)
    have alpha_nf_as:
      "None \<notin> dom (dist (execute
        (mmap (replicate (length as) ?round)) replay_state))"
      by (subst replay_update) (rule alpha_nf_start)
    show ?thesis
      using alpha_nf_as len_as by simp
  qed
  show ?thesis
  proof (rule no_failure_bindI[OF alpha_nf])
    fix as' s_alpha
    assume alpha_out:
      "Some (as', s_alpha) \<in>
        set_dist (execute (mmap (replicate (length spec) ?round)) replay_state)"
    have alpha_start:
      "Some (as', s_alpha) \<in>
        set_dist (execute (mmap (replicate (length as) ?round))
          (replay_state\<lparr>PTranscript := as @ [?dg] @ roots @ [final_msg] @ rest\<rparr>))"
    proof -
      have alpha_out_as:
        "Some (as', s_alpha) \<in>
          set_dist (execute (mmap (replicate (length as) ?round)) replay_state)"
        using alpha_out len_as by simp
      have replay_update:
        "replay_state =
          replay_state\<lparr>PTranscript := as @ [?dg] @ roots @ [final_msg] @ rest\<rparr>"
        using prefix by (simp add: append_assoc)
      show ?thesis
        by (subst replay_update[symmetric]) (rule alpha_out_as)
    qed
    have alpha_res:
      "as' = as \<and>
       PState s_alpha = foldl concat (PState replay_state) as \<and>
       PTranscript s_alpha = ?dg # roots @ [final_msg] @ rest \<and>
       PCompositionFriCounter s_alpha = PCompositionFriCounter replay_state \<and>
       replay_state \<le> s_alpha"
      using honest_alpha_mmap_replay_outcome[OF alpha_lookups alpha_start] by simp
    show "None \<notin> dom (dist (execute
      (p.read \<bind>
        (\<lambda>dg. assert (to_nat dg \<le> p.maxDegree) \<bind>
            (\<lambda>_. ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1)) \<bind>
            (\<lambda>fl. p.read \<bind> (\<lambda>final. return (as', dg, fl, final)))))) s_alpha))"
    proof (rule no_failure_bindI)
      show "None \<notin> dom (dist (execute p.read s_alpha))"
        by (rule p.read_no_failure) (use alpha_res in simp)
    next
      fix dg s_dg
      assume read_dg: "Some (dg, s_dg) \<in> set_dist (execute p.read s_alpha)"
      have read_dg':
        "Some (dg, s_dg) \<in>
          set_dist (execute p.read (s_alpha\<lparr>PTranscript := ?dg # roots @ [final_msg] @ rest\<rparr>))"
      proof -
        have s_alpha_update:
          "s_alpha = s_alpha\<lparr>PTranscript := ?dg # roots @ [final_msg] @ rest\<rparr>"
          using alpha_res by simp
        then show ?thesis
          by (subst s_alpha_update[symmetric]) (rule read_dg)
      qed
      have dg_res:
        "dg = ?dg \<and>
         s_dg = s_alpha\<lparr>PState := concat (PState s_alpha) ?dg,
           PTranscript := roots @ [final_msg] @ rest\<rparr>"
        using p.read_cons_outcome[OF read_dg'] by simp
      have degree_ok: "to_nat dg \<le> p.maxDegree"
        using honest_degree_message_assert_hol[OF htv, of as] dg_res by simp
      have rounds_eq: "ceil_log (to_nat dg + 1) = length roots"
        using honest_degree_message_rounds[OF htv, of as] dg_res roots_rounds by simp
      have fri_lookups_dg:
        "\<forall>i < length roots.
          fmlookup (HashMap s_dg)
            (CompositionFriChallenge
              (PCompositionFriCounter s_dg + i)
              (foldl concat (PState s_dg) (take (Suc i) roots))) =
            Some (challenges ! i)"
      proof (intro allI impI)
        fix i
        assume i_bound: "i < length roots"
        have lookup_replay:
          "fmlookup (HashMap replay_state)
            (CompositionFriChallenge (PCompositionFriCounter replay_state + i) (foldl concat
              (concat (foldl concat (PState replay_state) as) ?dg)
              (take (Suc i) roots))) =
            Some (challenges ! i)"
          using fri_lookups i_bound by simp
        have replay_s_dg: "replay_state \<le> s_dg"
        proof -
          have s_alpha_s_dg: "s_alpha \<le> s_dg"
            using dg_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
          show ?thesis
            using alpha_res s_alpha_s_dg by (meson p.hash_ext_trans)
        qed
        show "fmlookup (HashMap s_dg)
            (CompositionFriChallenge
              (PCompositionFriCounter s_dg + i)
              (foldl concat (PState s_dg) (take (Suc i) roots))) =
          Some (challenges ! i)"
          using p.hash_extension_lookup[OF lookup_replay replay_s_dg] alpha_res dg_res
          by simp
      qed
      have fri_nf_start:
        "None \<notin> dom (dist (execute
          (ntimes v.receive_composition_fri_commits (length roots))
          (s_dg\<lparr>PTranscript := roots @ ([final_msg] @ rest)\<rparr>)))"
        using honest_receive_composition_fri_commits_list_no_failure[
          OF fri_lookups_dg len_challenges, of "[final_msg] @ rest"] .
      have fri_nf:
        "None \<notin> dom (dist (execute
          (ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1))) s_dg))"
        using fri_nf_start dg_res rounds_eq by simp
      have cont_nf:
        "None \<notin> dom (dist (execute
          (ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1)) \<bind>
            (\<lambda>fl. p.read \<bind> (\<lambda>final. return (as', dg, fl, final)))) s_dg))"
      proof (rule no_failure_bindI[OF fri_nf])
        fix fl t
        assume fri_out:
          "Some (fl, t) \<in>
            set_dist (execute
              (ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1))) s_dg)"
        have fri_out_start:
          "Some (fl, t) \<in>
            set_dist (execute
              (ntimes v.receive_composition_fri_commits (length roots))
              (s_dg\<lparr>PTranscript := roots @ ([final_msg] @ rest)\<rparr>))"
          using fri_out dg_res rounds_eq by simp
        have tr_t: "PTranscript t = final_msg # rest"
          using honest_receive_composition_fri_commits_list_outcome[
            OF fri_lookups_dg len_challenges fri_out_start]
          by simp
        show "None \<notin> dom
          (dist (execute (p.read \<bind>
            (\<lambda>final. return (as', dg, fl, final))) t))"
          by (rule no_failure_bind_returnI)
            (rule p.read_no_failure, simp add: tr_t)
      qed
      show "None \<notin> dom (dist (execute
        (assert (to_nat dg \<le> p.maxDegree) \<bind>
          (\<lambda>_. ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1)) \<bind>
            (\<lambda>fl. p.read \<bind> (\<lambda>final. return (as', dg, fl, final))))) s_dg))"
        using degree_ok cont_nf by (simp add: assert_def)
    qed
  qed
qed

lemma honest_trace_root_alpha_degree_fri_final_dynamic_prefix_outcome:
  assumes htv: "honest_trace_valid"
    and len_as: "length as = length spec"
    and len_f_challenges: "length f_challenges = length f_roots"
    and f_roots_rounds: "length f_roots = ceil_log clength"
    and len_challenges: "length challenges = length roots"
    and roots_rounds:
      "length roots = ceil_log (degree (p.cp as p.f_powers) + 1)"
    and prefix:
      "PTranscript replay_state =
        value f_merkle # f_roots @ [f_final_msg] @
          as @ [of_nat (degree (p.cp as p.f_powers))] @ roots @ [final_msg] @ rest"
    and f_fri_lookups:
      "\<forall>i < length f_roots.
        fmlookup (HashMap replay_state)
          (TraceFriChallenge (PTraceFriCounter replay_state + i) (foldl concat
            (concat (PState replay_state) (value f_merkle))
            (take (Suc i) f_roots))) =
          Some (f_challenges ! i)"
    and alpha_lookups:
      "\<forall>i < length as.
        fmlookup (HashMap replay_state)
          (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat
            (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
              f_final_msg)
            (take i as))) =
          Some (as ! i)"
    and fri_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap replay_state)
          (CompositionFriChallenge (PCompositionFriCounter replay_state + i) (foldl concat
            (concat
              (foldl concat
                (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
                  f_final_msg)
                as)
              (of_nat (degree (p.cp as p.f_powers))))
            (take (Suc i) roots))) =
          Some (challenges ! i)"
    and outcome:
      "Some ((fr, f_fl, f_final, as', dg, fl, final), t) \<in> set_dist (execute
        (do {
          fr \<leftarrow> p.read;
          f_fl \<leftarrow> ntimes v.receive_trace_fri_commits (ceil_log clength);
          f_final \<leftarrow> p.read;
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
          fl \<leftarrow> ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1));
          final \<leftarrow> p.read;
          return (fr, f_fl, f_final, as', dg, fl, final)
        }) replay_state)"
  shows
    "fr = value f_merkle \<and>
     f_fl = zip f_challenges f_roots \<and>
     f_final = f_final_msg \<and>
     as' = as \<and>
     dg = of_nat (degree (p.cp as p.f_powers)) \<and>
     fl = zip challenges roots \<and>
     final = final_msg \<and>
     PState t =
       concat
         (foldl concat
           (concat
             (foldl concat
               (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
                 f_final_msg)
               as)
             (of_nat (degree (p.cp as p.f_powers))))
           roots)
         final_msg \<and>
     PTranscript t = rest \<and>
     replay_state \<le> t"
proof -
  let ?dg = "of_nat (degree (p.cp as p.f_powers))"
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  let ?tail =
    "do {
      as' \<leftarrow> mmap (replicate (length spec) ?round);
      dg \<leftarrow> p.read;
      assert (to_nat dg \<le> p.maxDegree);
      fl \<leftarrow> ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1));
      final \<leftarrow> p.read;
      return (as', dg, fl, final)
    }"
  from outcome obtain s_root s_fri s_trace s_alpha s_dg s_assert s_comp where
    read_fr: "Some (fr, s_root) \<in> set_dist (execute p.read replay_state)"
    and trace_fri_out:
      "Some (f_fl, s_fri) \<in>
        set_dist (execute
          (ntimes v.receive_trace_fri_commits (ceil_log clength)) s_root)"
    and read_f_final: "Some (f_final, s_trace) \<in> set_dist (execute p.read s_fri)"
    and alpha_out:
      "Some (as', s_alpha) \<in>
        set_dist (execute (mmap (replicate (length spec) ?round)) s_trace)"
    and read_dg: "Some (dg, s_dg) \<in> set_dist (execute p.read s_alpha)"
    and assert_dg:
      "Some ((), s_assert) \<in> set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s_dg)"
    and fri_out:
      "Some (fl, s_comp) \<in>
        set_dist (execute
          (ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1)))
          s_assert)"
    and read_final: "Some (final, t) \<in> set_dist (execute p.read s_comp)"
    by (auto elim!: p.set_dist_bindE)
  have tail_out:
    "Some ((as', dg, fl, final), t) \<in> set_dist (execute ?tail s_trace)"
    apply (rule set_dist_bindI[OF alpha_out])
    apply (rule set_dist_bindI[OF read_dg])
    apply (rule set_dist_bindI[OF assert_dg])
    apply (rule set_dist_bindI[OF fri_out])
    apply (rule set_dist_bindI[OF read_final])
    by simp
  have read_fr':
    "Some (fr, s_root) \<in>
      set_dist (execute p.read
        (replay_state\<lparr>PTranscript :=
          value f_merkle # (f_roots @ [f_final_msg] @ as @ [?dg] @ roots @ [final_msg] @ rest)\<rparr>))"
  proof -
    have replay_update:
      "replay_state =
        replay_state\<lparr>PTranscript :=
          value f_merkle # (f_roots @ [f_final_msg] @ as @ [?dg] @ roots @ [final_msg] @ rest)\<rparr>"
      using prefix by simp
    show ?thesis
      by (subst replay_update[symmetric]) (rule read_fr)
  qed
  have read_fr_res:
    "fr = value f_merkle \<and>
     s_root =
       replay_state\<lparr>PState := concat (PState replay_state) (value f_merkle),
         PTranscript := f_roots @ [f_final_msg] @ as @ [?dg] @ roots @ [final_msg] @ rest\<rparr>"
    using p.read_cons_outcome[OF read_fr'] by simp
  have f_fri_lookups_root:
    "\<forall>i < length f_roots.
      fmlookup (HashMap s_root)
        (TraceFriChallenge
          (PTraceFriCounter s_root + i)
          (foldl concat (PState s_root) (take (Suc i) f_roots))) =
        Some (f_challenges ! i)"
    using f_fri_lookups read_fr_res by simp
  have trace_fri_out':
    "Some (f_fl, s_fri) \<in>
      set_dist (execute (ntimes v.receive_trace_fri_commits (length f_roots))
        (s_root\<lparr>PTranscript := f_roots @ ([f_final_msg] @ as @ [?dg] @ roots @ [final_msg] @ rest)\<rparr>))"
    using trace_fri_out f_roots_rounds read_fr_res by simp
  have trace_fri_res:
    "f_fl = zip f_challenges f_roots \<and>
     PState s_fri = foldl concat (PState s_root) f_roots \<and>
     PTranscript s_fri = [f_final_msg] @ as @ [?dg] @ roots @ [final_msg] @ rest \<and>
     s_root \<le> s_fri"
    using honest_receive_trace_fri_commits_list_outcome[
      OF f_fri_lookups_root len_f_challenges trace_fri_out'] .
  have trace_fri_counters:
    "PCompositionFriCounter s_fri = PCompositionFriCounter s_root \<and>
     PAlphaCounter s_fri = PAlphaCounter s_root \<and>
     PQueryCounter s_fri = PQueryCounter s_root"
    using receive_trace_fri_commits_preserves_other_counters[OF trace_fri_out']
    by simp
  have read_f_final':
    "Some (f_final, s_trace) \<in>
      set_dist (execute p.read (s_fri\<lparr>PTranscript :=
        f_final_msg # (as @ [?dg] @ roots @ [final_msg] @ rest)\<rparr>))"
  proof -
    have s_fri_update:
      "s_fri =
        s_fri\<lparr>PTranscript := f_final_msg # (as @ [?dg] @ roots @ [final_msg] @ rest)\<rparr>"
      using trace_fri_res by simp
    show ?thesis
      by (subst s_fri_update[symmetric]) (rule read_f_final)
  qed
  have read_f_final_res:
    "f_final = f_final_msg \<and>
     s_trace =
       s_fri\<lparr>PState := concat (PState s_fri) f_final_msg,
         PTranscript := as @ [?dg] @ roots @ [final_msg] @ rest\<rparr>"
    using p.read_cons_outcome[OF read_f_final'] by simp
  have s_trace_counters:
    "PCompositionFriCounter s_trace = PCompositionFriCounter replay_state \<and>
     PAlphaCounter s_trace = PAlphaCounter replay_state"
    using read_fr_res trace_fri_counters read_f_final_res by simp
  have replay_s_trace: "replay_state \<le> s_trace"
  proof -
    have replay_root: "replay_state \<le> s_root"
      using read_fr_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    have s_fri_trace: "s_fri \<le> s_trace"
      using read_f_final_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    show ?thesis
      using replay_root trace_fri_res s_fri_trace by (meson p.hash_ext_trans)
  qed
  have alpha_lookups_trace:
    "\<forall>i < length as.
      fmlookup (HashMap s_trace)
        (AlphaChallenge (PAlphaCounter s_trace + i)
          (foldl concat (PState s_trace) (take i as))) =
        Some (as ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length as"
    have lookup_replay:
      "fmlookup (HashMap replay_state)
        (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat
          (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
            f_final_msg)
          (take i as))) =
        Some (as ! i)"
      using alpha_lookups i_bound by simp
    show "fmlookup (HashMap s_trace)
      (AlphaChallenge (PAlphaCounter s_trace + i)
        (foldl concat (PState s_trace) (take i as))) =
      Some (as ! i)"
      using p.hash_extension_lookup[OF lookup_replay replay_s_trace]
        read_fr_res trace_fri_res read_f_final_res s_trace_counters
      by simp
  qed
  have fri_lookups_trace:
    "\<forall>i < length roots.
      fmlookup (HashMap s_trace)
        (CompositionFriChallenge (PCompositionFriCounter s_trace + i) (foldl concat
          (concat (foldl concat (PState s_trace) as) ?dg)
          (take (Suc i) roots))) =
        Some (challenges ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length roots"
    have lookup_replay:
      "fmlookup (HashMap replay_state)
        (CompositionFriChallenge (PCompositionFriCounter replay_state + i) (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
                f_final_msg)
              as)
            ?dg)
          (take (Suc i) roots))) =
        Some (challenges ! i)"
      using fri_lookups i_bound by simp
    show "fmlookup (HashMap s_trace)
      (CompositionFriChallenge (PCompositionFriCounter s_trace + i) (foldl concat
        (concat (foldl concat (PState s_trace) as) ?dg)
        (take (Suc i) roots))) =
      Some (challenges ! i)"
      using p.hash_extension_lookup[OF lookup_replay replay_s_trace]
        read_fr_res trace_fri_res read_f_final_res s_trace_counters
      by simp
  qed
  have tail_prefix:
    "PTranscript s_trace = as @ [?dg] @ roots @ [final_msg] @ rest"
    using read_f_final_res by simp
  have tail_res:
    "as' = as \<and>
     dg = ?dg \<and>
     fl = zip challenges roots \<and>
     final = final_msg \<and>
     PState t =
       concat
         (foldl concat
           (concat (foldl concat (PState s_trace) as) ?dg)
           roots)
         final_msg \<and>
     PTranscript t = rest \<and>
     s_trace \<le> t"
    by (rule honest_alpha_degree_fri_final_dynamic_prefix_outcome[
        OF htv len_as len_challenges roots_rounds tail_prefix
          alpha_lookups_trace fri_lookups_trace tail_out])
  have replay_t: "replay_state \<le> t"
  proof -
    have replay_root: "replay_state \<le> s_root"
      using read_fr_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    have s_fri_trace: "s_fri \<le> s_trace"
      using read_f_final_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    show ?thesis
      using replay_root trace_fri_res s_fri_trace tail_res by (meson p.hash_ext_trans)
  qed
	  show ?thesis
	    using read_fr_res trace_fri_res read_f_final_res tail_res replay_t by simp
	qed

lemma honest_trace_root_alpha_degree_fri_final_dynamic_prefix_preserves_query_counter:
  assumes outcome:
    "Some ((fr, f_fl, f_final, as', dg, fl, final), t) \<in> set_dist (execute
      (do {
        fr \<leftarrow> p.read;
        f_fl \<leftarrow> ntimes v.receive_trace_fri_commits (ceil_log clength);
        f_final \<leftarrow> p.read;
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
        fl \<leftarrow> ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1));
        final \<leftarrow> p.read;
        return (fr, f_fl, f_final, as', dg, fl, final)
      }) s)"
  shows "PQueryCounter t = PQueryCounter s"
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
  from outcome obtain s_root s_fri s_trace s_alpha s_dg s_assert s_comp where
    read_fr: "Some (fr, s_root) \<in> set_dist (execute p.read s)"
    and trace_fri_out:
      "Some (f_fl, s_fri) \<in>
        set_dist (execute (ntimes v.receive_trace_fri_commits (ceil_log clength)) s_root)"
    and read_f_final: "Some (f_final, s_trace) \<in> set_dist (execute p.read s_fri)"
    and alpha_out:
      "Some (as', s_alpha) \<in>
        set_dist (execute (mmap (replicate (length spec) ?round)) s_trace)"
    and read_dg: "Some (dg, s_dg) \<in> set_dist (execute p.read s_alpha)"
    and assert_dg:
      "Some ((), s_assert) \<in> set_dist (execute (assert (to_nat dg \<le> p.maxDegree)) s_dg)"
    and comp_out:
      "Some (fl, s_comp) \<in>
        set_dist (execute
          (ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1))) s_assert)"
    and read_final: "Some (final, t) \<in> set_dist (execute p.read s_comp)"
    by (auto elim!: p.set_dist_bindE)
  have q_root: "PQueryCounter s_root = PQueryCounter s"
    using read_preserves_counters[OF read_fr] by simp
  have q_fri: "PQueryCounter s_fri = PQueryCounter s_root"
    using receive_trace_fri_commits_preserves_other_counters[OF trace_fri_out] by simp
  have q_trace: "PQueryCounter s_trace = PQueryCounter s_fri"
    using read_preserves_counters[OF read_f_final] by simp
  have q_alpha: "PQueryCounter s_alpha = PQueryCounter s_trace"
    by (rule honest_alpha_mmap_replay_preserves_query_counter[OF alpha_out])
  have q_dg: "PQueryCounter s_dg = PQueryCounter s_alpha"
    using read_preserves_counters[OF read_dg] by simp
  have s_assert_eq: "s_assert = s_dg"
    using assert_outcomeD(2)[OF assert_dg] .
  have q_comp: "PQueryCounter s_comp = PQueryCounter s_assert"
    using receive_composition_fri_commits_preserves_other_counters[OF comp_out] by simp
  have q_final: "PQueryCounter t = PQueryCounter s_comp"
    using read_preserves_counters[OF read_final] by simp
  show ?thesis
    using q_root q_fri q_trace q_alpha q_dg q_comp q_final
    unfolding s_assert_eq by simp
qed

lemma honest_trace_root_alpha_degree_fri_final_dynamic_prefix_no_failure:
  assumes htv: "honest_trace_valid"
    and len_as: "length as = length spec"
    and len_f_challenges: "length f_challenges = length f_roots"
    and f_roots_rounds: "length f_roots = ceil_log clength"
    and len_challenges: "length challenges = length roots"
    and roots_rounds:
      "length roots = ceil_log (degree (p.cp as p.f_powers) + 1)"
    and prefix:
      "PTranscript replay_state =
        value f_merkle # f_roots @ [f_final_msg] @
          as @ [of_nat (degree (p.cp as p.f_powers))] @ roots @ [final_msg] @ rest"
    and f_fri_lookups:
      "\<forall>i < length f_roots.
        fmlookup (HashMap replay_state)
          (TraceFriChallenge (PTraceFriCounter replay_state + i) (foldl concat
            (concat (PState replay_state) (value f_merkle))
            (take (Suc i) f_roots))) =
          Some (f_challenges ! i)"
    and alpha_lookups:
      "\<forall>i < length as.
        fmlookup (HashMap replay_state)
          (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat
            (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
              f_final_msg)
            (take i as))) =
          Some (as ! i)"
    and fri_lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap replay_state)
          (CompositionFriChallenge (PCompositionFriCounter replay_state + i) (foldl concat
            (concat
              (foldl concat
                (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
                  f_final_msg)
                as)
              (of_nat (degree (p.cp as p.f_powers))))
            (take (Suc i) roots))) =
          Some (challenges ! i)"
  shows
    "None \<notin> dom (dist (execute
      (do {
        fr \<leftarrow> p.read;
        f_fl \<leftarrow> ntimes v.receive_trace_fri_commits (ceil_log clength);
        f_final \<leftarrow> p.read;
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
        fl \<leftarrow> ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1));
        final \<leftarrow> p.read;
        return (fr, f_fl, f_final, as', dg, fl, final)
      }) replay_state))"
proof -
  let ?dg = "of_nat (degree (p.cp as p.f_powers))"
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  show ?thesis
  proof (rule no_failure_bindI)
    show "None \<notin> dom (dist (execute p.read replay_state))"
      by (rule p.read_no_failure) (use prefix in simp)
  next
    fix fr s_root
    assume read_fr: "Some (fr, s_root) \<in> set_dist (execute p.read replay_state)"
    have read_fr':
      "Some (fr, s_root) \<in>
        set_dist (execute p.read
          (replay_state\<lparr>PTranscript :=
            value f_merkle # (f_roots @ [f_final_msg] @ as @ [?dg] @ roots @ [final_msg] @ rest)\<rparr>))"
    proof -
      have replay_update:
        "replay_state =
          replay_state\<lparr>PTranscript :=
            value f_merkle # (f_roots @ [f_final_msg] @ as @ [?dg] @ roots @ [final_msg] @ rest)\<rparr>"
        using prefix by simp
      show ?thesis
        by (subst replay_update[symmetric]) (rule read_fr)
    qed
    have read_fr_res:
      "s_root =
        replay_state\<lparr>PState := concat (PState replay_state) (value f_merkle),
          PTranscript := f_roots @ [f_final_msg] @ as @ [?dg] @ roots @ [final_msg] @ rest\<rparr>"
      using p.read_cons_outcome[OF read_fr'] by simp
    have f_fri_lookups_root:
      "\<forall>i < length f_roots.
        fmlookup (HashMap s_root)
          (TraceFriChallenge
            (PTraceFriCounter s_root + i)
            (foldl concat (PState s_root) (take (Suc i) f_roots))) =
          Some (f_challenges ! i)"
      using f_fri_lookups read_fr_res by simp
    have trace_fri_nf_start:
      "None \<notin> dom (dist (execute
        (ntimes v.receive_trace_fri_commits (length f_roots))
        (s_root\<lparr>PTranscript := f_roots @ ([f_final_msg] @ as @ [?dg] @ roots @ [final_msg] @ rest)\<rparr>)))"
      using honest_receive_trace_fri_commits_list_no_failure[
        OF f_fri_lookups_root len_f_challenges, of "[f_final_msg] @ as @ [?dg] @ roots @ [final_msg] @ rest"] .
    have trace_fri_nf:
      "None \<notin> dom (dist (execute
        (ntimes v.receive_trace_fri_commits (ceil_log clength)) s_root))"
      using trace_fri_nf_start f_roots_rounds read_fr_res by simp
    show "None \<notin> dom (dist (execute
      (ntimes v.receive_trace_fri_commits (ceil_log clength) \<bind>
        (\<lambda>f_fl. p.read \<bind>
          (\<lambda>f_final. mmap (replicate (length spec) ?round) \<bind>
            (\<lambda>as'. p.read \<bind>
              (\<lambda>dg. assert (to_nat dg \<le> p.maxDegree) \<bind>
                (\<lambda>_. ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1)) \<bind>
                  (\<lambda>fl. p.read \<bind>
                    (\<lambda>final. return (fr, f_fl, f_final, as', dg, fl, final))))))))) s_root))"
    proof (rule no_failure_bindI[OF trace_fri_nf])
      fix f_fl s_fri
      assume trace_fri_out:
        "Some (f_fl, s_fri) \<in>
          set_dist (execute
            (ntimes v.receive_trace_fri_commits (ceil_log clength)) s_root)"
      have trace_fri_out':
        "Some (f_fl, s_fri) \<in>
          set_dist (execute (ntimes v.receive_trace_fri_commits (length f_roots))
            (s_root\<lparr>PTranscript := f_roots @ ([f_final_msg] @ as @ [?dg] @ roots @ [final_msg] @ rest)\<rparr>))"
        using trace_fri_out f_roots_rounds read_fr_res by simp
      have trace_fri_res:
        "PState s_fri = foldl concat (PState s_root) f_roots \<and>
         PTranscript s_fri = [f_final_msg] @ as @ [?dg] @ roots @ [final_msg] @ rest \<and>
         s_root \<le> s_fri"
        using honest_receive_trace_fri_commits_list_outcome[
          OF f_fri_lookups_root len_f_challenges trace_fri_out'] by simp
      have trace_fri_counters:
        "PCompositionFriCounter s_fri = PCompositionFriCounter s_root \<and>
         PAlphaCounter s_fri = PAlphaCounter s_root \<and>
         PQueryCounter s_fri = PQueryCounter s_root"
        using receive_trace_fri_commits_preserves_other_counters[OF trace_fri_out']
        by simp
      show "None \<notin> dom (dist (execute
        (p.read \<bind>
          (\<lambda>f_final. mmap (replicate (length spec) ?round) \<bind>
            (\<lambda>as'. p.read \<bind>
              (\<lambda>dg. assert (to_nat dg \<le> p.maxDegree) \<bind>
                (\<lambda>_. ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1)) \<bind>
                  (\<lambda>fl. p.read \<bind>
                    (\<lambda>final. return (fr, f_fl, f_final, as', dg, fl, final)))))))) s_fri))"
      proof (rule no_failure_bindI)
        show "None \<notin> dom (dist (execute p.read s_fri))"
          by (rule p.read_no_failure) (use trace_fri_res in simp)
      next
        fix f_final s_trace
        assume read_f_final: "Some (f_final, s_trace) \<in> set_dist (execute p.read s_fri)"
        have read_f_final':
          "Some (f_final, s_trace) \<in>
            set_dist (execute p.read (s_fri\<lparr>PTranscript :=
              f_final_msg # (as @ [?dg] @ roots @ [final_msg] @ rest)\<rparr>))"
        proof -
          have s_fri_update:
            "s_fri =
              s_fri\<lparr>PTranscript := f_final_msg # (as @ [?dg] @ roots @ [final_msg] @ rest)\<rparr>"
            using trace_fri_res by simp
          show ?thesis
            by (subst s_fri_update[symmetric]) (rule read_f_final)
        qed
        have read_f_final_res:
          "s_trace =
            s_fri\<lparr>PState := concat (PState s_fri) f_final_msg,
              PTranscript := as @ [?dg] @ roots @ [final_msg] @ rest\<rparr>"
          using p.read_cons_outcome[OF read_f_final'] by simp
        have s_trace_counters:
          "PCompositionFriCounter s_trace = PCompositionFriCounter replay_state \<and>
           PAlphaCounter s_trace = PAlphaCounter replay_state"
          using read_fr_res trace_fri_counters read_f_final_res by simp
        have replay_s_trace: "replay_state \<le> s_trace"
        proof -
          have replay_root: "replay_state \<le> s_root"
            using read_fr_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
          have s_fri_trace: "s_fri \<le> s_trace"
            using read_f_final_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
          show ?thesis
            using replay_root trace_fri_res s_fri_trace by (meson p.hash_ext_trans)
        qed
        have alpha_lookups_trace:
          "\<forall>i < length as.
            fmlookup (HashMap s_trace)
              (AlphaChallenge (PAlphaCounter s_trace + i)
                (foldl concat (PState s_trace) (take i as))) =
              Some (as ! i)"
        proof (intro allI impI)
          fix i
          assume i_bound: "i < length as"
          have lookup_replay:
            "fmlookup (HashMap replay_state)
              (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat
                (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
                  f_final_msg)
                (take i as))) =
              Some (as ! i)"
            using alpha_lookups i_bound by simp
          show "fmlookup (HashMap s_trace)
            (AlphaChallenge (PAlphaCounter s_trace + i)
              (foldl concat (PState s_trace) (take i as))) =
            Some (as ! i)"
            using p.hash_extension_lookup[OF lookup_replay replay_s_trace]
              read_fr_res trace_fri_res read_f_final_res s_trace_counters
            by simp
        qed
        have fri_lookups_trace:
          "\<forall>i < length roots.
            fmlookup (HashMap s_trace)
              (CompositionFriChallenge (PCompositionFriCounter s_trace + i) (foldl concat
                (concat (foldl concat (PState s_trace) as) ?dg)
                (take (Suc i) roots))) =
              Some (challenges ! i)"
        proof (intro allI impI)
          fix i
          assume i_bound: "i < length roots"
          have lookup_replay:
            "fmlookup (HashMap replay_state)
              (CompositionFriChallenge (PCompositionFriCounter replay_state + i) (foldl concat
                (concat
                  (foldl concat
                    (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
                      f_final_msg)
                    as)
                  ?dg)
                (take (Suc i) roots))) =
              Some (challenges ! i)"
            using fri_lookups i_bound by simp
          show "fmlookup (HashMap s_trace)
            (CompositionFriChallenge (PCompositionFriCounter s_trace + i) (foldl concat
              (concat (foldl concat (PState s_trace) as) ?dg)
              (take (Suc i) roots))) =
            Some (challenges ! i)"
            using p.hash_extension_lookup[OF lookup_replay replay_s_trace]
              read_fr_res trace_fri_res read_f_final_res s_trace_counters
            by simp
        qed
        have tail_prefix:
          "PTranscript s_trace = as @ [?dg] @ roots @ [final_msg] @ rest"
          using read_f_final_res by simp
        have tail_nf:
          "None \<notin> dom (dist (execute
            (do {
              as' \<leftarrow> mmap (replicate (length spec) ?round);
              dg \<leftarrow> p.read;
              assert (to_nat dg \<le> p.maxDegree);
              fl \<leftarrow> ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1));
              final \<leftarrow> p.read;
              return (as', dg, fl, final)
            }) s_trace))"
          by (rule honest_alpha_degree_fri_final_dynamic_prefix_no_failure[
              OF htv len_as len_challenges roots_rounds tail_prefix
                alpha_lookups_trace fri_lookups_trace])
        show "None \<notin> dom (dist (execute
          (mmap (replicate (length spec) ?round) \<bind>
            (\<lambda>as'. p.read \<bind>
              (\<lambda>dg. assert (to_nat dg \<le> p.maxDegree) \<bind>
                (\<lambda>_. ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1)) \<bind>
                  (\<lambda>fl. p.read \<bind>
                    (\<lambda>final. return (fr, f_fl, f_final, as', dg, fl, final))))))) s_trace))"
        proof -
          let ?tail =
            "do {
              as' \<leftarrow> mmap (replicate (length spec) ?round);
              dg \<leftarrow> p.read;
              assert (to_nat dg \<le> p.maxDegree);
              fl \<leftarrow> ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1));
              final \<leftarrow> p.read;
              return (as', dg, fl, final)
            }"
          have tail_full_eq:
            "(mmap (replicate (length spec) ?round) \<bind>
              (\<lambda>as'. p.read \<bind>
                (\<lambda>dg. assert (to_nat dg \<le> p.maxDegree) \<bind>
                  (\<lambda>_. ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1)) \<bind>
                    (\<lambda>fl. p.read \<bind>
                      (\<lambda>final. return (fr, f_fl, f_final, as', dg, fl, final))))))) =
             (?tail \<bind>
               (\<lambda>out. return (case out of (as', dg, fl, final) \<Rightarrow>
                 (fr, f_fl, f_final, as', dg, fl, final))))"
            by (simp add: sm_bind_assoc split: prod.splits)
          show ?thesis
            unfolding tail_full_eq
            by (rule no_failure_bind_returnI[OF tail_nf])
        qed
      qed
    qed
  qed
qed

lemma honest_trace_root_alpha_degree_fri_final_dynamic_from_prover_tail_no_failure:
  assumes htv: "honest_trace_valid"
    and create_f:
      "Some (f_merkle, s1) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and send_f:
      "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
    and f_nrounds_def: "f_nrounds = ceil_log clength"
    and trace_fri:
      "Some ((f_ps, f_ds, f_ls, f_ms), s_trace_fri) \<in>
        set_dist (execute
          (p.trace_fri_commit f_nrounds [p.f] [p.eval_domain] [p.f_eval] [f_merkle]) s2)"
    and trace_final_send:
      "Some ((), s_trace_final) \<in>
        set_dist (execute (p.send (hd (last f_ls))) s_trace_fri)"
    and alphas:
      "Some (as, s3) \<in>
        set_dist (execute
          (mmap (replicate (length spec)
            (do {
              a \<leftarrow> p.receive_alpha_challenge;
              p.send a;
              return a
            }))) s_trace_final)"
    and cp'_def: "cp' = p.cp as p.f_powers"
    and send_degree:
      "Some ((), s4) \<in> set_dist (execute (p.send (of_nat (degree cp'))) s3)"
    and create_cp:
      "Some (cp_merkle, s5) \<in> set_dist (execute (p.create (p.cp_eval as)) s4)"
    and nrounds_def: "nrounds = ceil_log (degree cp' + 1)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.composition_fri_commit nrounds [cp'] [p.eval_domain] [p.cp_eval as] [cp_merkle]) s5)"
    and final_send:
      "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    and tail:
      "Some (prover_result, prover_state) \<in>
        set_dist (execute (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds) s_final)"
    and replay: "replay_state = verifier_replay_state prover_state"
  shows
    "None \<notin> dom (dist (execute
      (do {
        fr \<leftarrow> p.read;
        f_fl \<leftarrow> ntimes v.receive_trace_fri_commits (ceil_log clength);
        f_final \<leftarrow> p.read;
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
        fl \<leftarrow> ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1));
        final \<leftarrow> p.read;
        return (fr, f_fl, f_final, as', dg, fl, final)
      }) replay_state))"
proof -
  from trace_fri_commit_initial_replay_successor_data[OF trace_fri] obtain f_roots f_challenges where
    f_len_roots: "length f_roots = f_nrounds"
    and f_len_challenges: "length f_challenges = f_nrounds"
    and tr_trace_fri: "PTranscript s_trace_fri = rev f_roots @ PTranscript s2"
    and st_trace_fri: "PState s_trace_fri = foldl concat (PState s2) f_roots"
	    and trace_fri_lookups_state:
	      "\<forall>i < length f_roots.
	        fmlookup (HashMap s_trace_fri)
	          (TraceFriChallenge (PTraceFriCounter s2 + i)
	            (foldl concat (PState s2) (take (Suc i) f_roots))) =
	          Some (f_challenges ! i)"
	    by blast
  from composition_fri_commit_initial_replay_successor_data[OF fri] obtain roots challenges where
    len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and tr_s6: "PTranscript s6 = rev roots @ PTranscript s5"
    and st_s6: "PState s6 = foldl concat (PState s5) roots"
	    and fri_lookups_s6:
	      "\<forall>i < length roots.
	        fmlookup (HashMap s6)
	          (CompositionFriChallenge
	            (PCompositionFriCounter s5 + i)
	            (foldl concat (PState s5) (take (Suc i) roots))) =
	          Some (challenges ! i)"
	    by blast
  have alpha_data:
    "length as = length spec \<and>
	     s_trace_final \<le> s3 \<and>
		     PState s3 = foldl concat (PState s_trace_final) as \<and>
		     PTranscript s3 = rev as @ PTranscript s_trace_final \<and>
         PCompositionFriCounter s3 = PCompositionFriCounter s_trace_final \<and>
		     (\<forall>i < length as.
		        fmlookup (HashMap s3)
		          (AlphaChallenge (PAlphaCounter s_trace_final + i)
	            (foldl concat (PState s_trace_final) (take i as))) =
	          Some (as ! i))"
    using alpha_mmap_outcome[OF alphas] by simp
  have tail_hash: "s_final \<le> prover_state"
    by (rule ntimes_hash_extends[OF _ tail])
      (rule prover_query_round_hash_extends)
  have s2_trace_fri: "s2 \<le> s_trace_fri"
    using p.trace_fri_commit_extends[OF trace_fri] .
  have trace_fri_final_hash: "s_trace_fri \<le> s_trace_final"
    using send_hash_extends[OF trace_final_send] .
  have s3_s4: "s3 \<le> s4"
    using send_hash_extends[OF send_degree] .
  have s4_s5: "s4 \<le> s5"
    using create_hash_extends[OF create_cp] .
  have s5_s6: "s5 \<le> s6"
    using p.composition_fri_commit_extends[OF fri] .
  have s6_final_hash: "s6 \<le> s_final"
    using send_hash_extends[OF final_send] .
  have trace_fri_prover: "s_trace_fri \<le> prover_state"
    using trace_fri_final_hash alpha_data s3_s4 s4_s5 s5_s6 s6_final_hash tail_hash
    by (meson p.hash_ext_trans)
  have s3_prover: "s3 \<le> prover_state"
    using s3_s4 s4_s5 s5_s6 s6_final_hash tail_hash by (meson p.hash_ext_trans)
  have s6_prover: "s6 \<le> prover_state"
    using s6_final_hash tail_hash by (rule p.hash_ext_trans)
  have final_tail_tr: "transcript_extends prover_state s_final"
    by (rule ntimes_transcript_extends[OF _ tail])
      (rule prover_query_round_transcript_extends)
  from final_tail_tr obtain ys where
    tr_prover: "PTranscript prover_state = ys @ PTranscript s_final"
    unfolding transcript_extends_def by auto
  have tr_s1: "PTranscript s1 = []"
    using create_preserves_transcript[OF create_f]
    unfolding init_state_def by simp
  have send_f_res:
    "s2 = s1\<lparr>
      PState := concat (PState s1) (value f_merkle),
      PTranscript := value f_merkle # PTranscript s1\<rparr>"
    using p.send_outcome[OF send_f] .
  have trace_final_res:
    "s_trace_final = s_trace_fri\<lparr>
      PState := concat (PState s_trace_fri) (hd (last f_ls)),
      PTranscript := hd (last f_ls) # PTranscript s_trace_fri\<rparr>"
    using p.send_outcome[OF trace_final_send] .
  have send_degree_res:
    "s4 = s3\<lparr>
      PState := concat (PState s3) (of_nat (degree cp')),
      PTranscript := of_nat (degree cp') # PTranscript s3\<rparr>"
    using p.send_outcome[OF send_degree] .
  have tr_s5: "PTranscript s5 = PTranscript s4"
    using create_preserves_transcript[OF create_cp] .
  have final_send_res:
    "s_final = s6\<lparr>
      PState := concat (PState s6) (hd (last ls)),
      PTranscript := hd (last ls) # PTranscript s6\<rparr>"
    using p.send_outcome[OF final_send] .
  have replay_prefix:
    "PTranscript replay_state =
      value f_merkle # f_roots @ [hd (last f_ls)] @
        as @ [of_nat (degree (p.cp as p.f_powers))] @ roots @ [hd (last ls)] @ rev ys"
    using replay tr_prover final_send_res tr_s6 tr_s5 send_degree_res alpha_data
      trace_final_res tr_trace_fri send_f_res tr_s1 cp'_def
    unfolding verifier_replay_state_def by simp
  have st_s1: "PState s1 = 0"
    using create_preserves_state[OF create_f]
    unfolding init_state_def by simp
  have st_trace_final:
    "PState s_trace_final =
      concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
        (hd (last f_ls))"
    using st_s1 send_f_res st_trace_fri trace_final_res replay
    unfolding verifier_replay_state_def by simp
  have st_s5:
    "PState s5 =
      concat
        (foldl concat
          (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
            (hd (last f_ls)))
          as)
        (of_nat (degree (p.cp as p.f_powers)))"
    using st_trace_final alpha_data send_degree_res create_preserves_state[OF create_cp] cp'_def
    by simp
  have trace_counter_s1_zero: "PTraceFriCounter s1 = 0"
    using p.create_preserves_channel(3)[OF create_f]
    unfolding init_state_def by simp
  have trace_counter_s2_zero: "PTraceFriCounter s2 = 0"
    using send_f_res trace_counter_s1_zero by simp
  have alpha_counter_s1_zero: "PAlphaCounter s1 = 0"
    using p.create_preserves_channel(5)[OF create_f]
    unfolding init_state_def by simp
  have alpha_counter_s2_zero: "PAlphaCounter s2 = 0"
    using send_f_res alpha_counter_s1_zero by simp
  have alpha_counter_trace_fri_zero: "PAlphaCounter s_trace_fri = 0"
    using trace_fri_commit_preserves_alpha_counter[OF trace_fri]
      alpha_counter_s2_zero by simp
  have alpha_counter_trace_final_zero: "PAlphaCounter s_trace_final = 0"
    using trace_final_res alpha_counter_trace_fri_zero by simp
  have comp_counter_s1_zero: "PCompositionFriCounter s1 = 0"
    using p.create_preserves_channel(4)[OF create_f]
    unfolding init_state_def by simp
  have comp_counter_s2_zero: "PCompositionFriCounter s2 = 0"
    using send_f_res comp_counter_s1_zero by simp
  have comp_counter_trace_fri_zero: "PCompositionFriCounter s_trace_fri = 0"
    using trace_fri_commit_preserves_composition_counter[OF trace_fri]
      comp_counter_s2_zero by simp
  have comp_counter_trace_final_zero:
    "PCompositionFriCounter s_trace_final = 0"
    using trace_final_res comp_counter_trace_fri_zero by simp
  have comp_counter_s3_zero: "PCompositionFriCounter s3 = 0"
    using alpha_data comp_counter_trace_final_zero by simp
  have comp_counter_s4_zero: "PCompositionFriCounter s4 = 0"
    using send_degree_res comp_counter_s3_zero by simp
  have comp_counter_s5_zero: "PCompositionFriCounter s5 = 0"
    using p.create_preserves_channel(4)[OF create_cp] comp_counter_s4_zero
    by simp
  have f_fri_lookups:
    "\<forall>i < length f_roots.
      fmlookup (HashMap replay_state)
        (TraceFriChallenge (PTraceFriCounter replay_state + i) (foldl concat
          (concat (PState replay_state) (value f_merkle))
          (take (Suc i) f_roots))) =
        Some (f_challenges ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length f_roots"
    have lookup_trace:
	      "fmlookup (HashMap s_trace_fri)
	        (TraceFriChallenge (PTraceFriCounter s2 + i)
	          (foldl concat (PState s2) (take (Suc i) f_roots))) =
	        Some (f_challenges ! i)"
      using trace_fri_lookups_state i_bound by simp
    have lookup_prover:
	      "fmlookup (HashMap prover_state)
	        (TraceFriChallenge (PTraceFriCounter s2 + i)
	          (foldl concat (PState s2) (take (Suc i) f_roots))) =
	        Some (f_challenges ! i)"
      using p.hash_extension_lookup[OF lookup_trace trace_fri_prover] .
    show "fmlookup (HashMap replay_state)
      (TraceFriChallenge (PTraceFriCounter replay_state + i) (foldl concat
        (concat (PState replay_state) (value f_merkle))
        (take (Suc i) f_roots))) =
      Some (f_challenges ! i)"
      using lookup_prover send_f_res st_s1 replay trace_counter_s2_zero
      unfolding verifier_replay_state_def by simp
  qed
  have alpha_lookups:
    "\<forall>i < length as.
      fmlookup (HashMap replay_state)
        (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat
          (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
            (hd (last f_ls)))
          (take i as))) =
        Some (as ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length as"
    have alpha_lookups_s3:
	      "\<forall>i < length as.
	        fmlookup (HashMap s3)
	          (AlphaChallenge (PAlphaCounter s_trace_final + i)
	            (foldl concat (PState s_trace_final) (take i as))) =
	          Some (as ! i)"
      using alpha_data by simp
    have lookup_s3:
	      "fmlookup (HashMap s3)
	        (AlphaChallenge (PAlphaCounter s_trace_final + i)
	          (foldl concat (PState s_trace_final) (take i as))) =
	        Some (as ! i)"
      using alpha_lookups_s3 i_bound by simp
    have lookup_prover:
	      "fmlookup (HashMap prover_state)
	        (AlphaChallenge (PAlphaCounter s_trace_final + i)
	          (foldl concat (PState s_trace_final) (take i as))) =
	        Some (as ! i)"
      using p.hash_extension_lookup[OF lookup_s3 s3_prover] .
    show "fmlookup (HashMap replay_state)
      (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat
        (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
          (hd (last f_ls)))
        (take i as))) =
      Some (as ! i)"
      using lookup_prover st_trace_final replay alpha_counter_trace_final_zero
      unfolding verifier_replay_state_def by simp
  qed
  have fri_lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap replay_state)
        (CompositionFriChallenge (PCompositionFriCounter replay_state + i) (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
                (hd (last f_ls)))
              as)
            (of_nat (degree (p.cp as p.f_powers))))
          (take (Suc i) roots))) =
        Some (challenges ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length roots"
    have lookup_s6:
	      "fmlookup (HashMap s6)
	        (CompositionFriChallenge
	          (PCompositionFriCounter s5 + i)
	          (foldl concat (PState s5) (take (Suc i) roots))) =
	        Some (challenges ! i)"
      using fri_lookups_s6 i_bound by simp
    have lookup_prover:
	      "fmlookup (HashMap prover_state)
	        (CompositionFriChallenge
	          (PCompositionFriCounter s5 + i)
	          (foldl concat (PState s5) (take (Suc i) roots))) =
	        Some (challenges ! i)"
      using p.hash_extension_lookup[OF lookup_s6 s6_prover] .
    show "fmlookup (HashMap replay_state)
      (CompositionFriChallenge (PCompositionFriCounter replay_state + i) (foldl concat
        (concat
          (foldl concat
            (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
              (hd (last f_ls)))
            as)
          (of_nat (degree (p.cp as p.f_powers))))
        (take (Suc i) roots))) =
      Some (challenges ! i)"
      using lookup_prover st_s5 replay comp_counter_s5_zero
      unfolding verifier_replay_state_def by simp
  qed
  have f_roots_rounds: "length f_roots = ceil_log clength"
    using f_len_roots f_nrounds_def by simp
  have f_len_challenges_roots: "length f_challenges = length f_roots"
    using f_len_challenges f_len_roots by simp
  have roots_rounds:
    "length roots = ceil_log (degree (p.cp as p.f_powers) + 1)"
    using len_roots nrounds_def cp'_def by simp
  have len_challenges_roots: "length challenges = length roots"
    using len_challenges len_roots by simp
  show ?thesis
    by (rule honest_trace_root_alpha_degree_fri_final_dynamic_prefix_no_failure[
        OF htv conjunct1[OF alpha_data] f_len_challenges_roots f_roots_rounds
          len_challenges_roots roots_rounds replay_prefix f_fri_lookups
          alpha_lookups fri_lookups])
qed

lemma honest_trace_root_alpha_degree_fri_final_dynamic_from_prover_tail_outcome:
  assumes htv: "honest_trace_valid"
    and create_f:
      "Some (f_merkle, s1) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and send_f:
      "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
    and f_nrounds_def: "f_nrounds = ceil_log clength"
    and trace_fri:
      "Some ((f_ps, f_ds, f_ls, f_ms), s_trace_fri) \<in>
        set_dist (execute
          (p.trace_fri_commit f_nrounds [p.f] [p.eval_domain] [p.f_eval] [f_merkle]) s2)"
    and trace_final_send:
      "Some ((), s_trace_final) \<in>
        set_dist (execute (p.send (hd (last f_ls))) s_trace_fri)"
    and alphas:
      "Some (as, s3) \<in>
        set_dist (execute
          (mmap (replicate (length spec)
            (do {
              a \<leftarrow> p.receive_alpha_challenge;
              p.send a;
              return a
            }))) s_trace_final)"
    and cp'_def: "cp' = p.cp as p.f_powers"
    and send_degree:
      "Some ((), s4) \<in> set_dist (execute (p.send (of_nat (degree cp'))) s3)"
    and create_cp:
      "Some (cp_merkle, s5) \<in> set_dist (execute (p.create (p.cp_eval as)) s4)"
    and nrounds_def: "nrounds = ceil_log (degree cp' + 1)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.composition_fri_commit nrounds [cp'] [p.eval_domain] [p.cp_eval as] [cp_merkle]) s5)"
    and final_send:
      "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    and tail:
      "Some (prover_result, prover_state) \<in>
        set_dist (execute (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds) s_final)"
    and replay: "replay_state = verifier_replay_state prover_state"
    and outcome:
      "Some ((fr, f_fl, f_final, as', dg, fl, final), t) \<in> set_dist (execute
        (do {
          fr \<leftarrow> p.read;
          f_fl \<leftarrow> ntimes v.receive_trace_fri_commits (ceil_log clength);
          f_final \<leftarrow> p.read;
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
          fl \<leftarrow> ntimes v.receive_composition_fri_commits (ceil_log (to_nat dg + 1));
          final \<leftarrow> p.read;
          return (fr, f_fl, f_final, as', dg, fl, final)
        }) replay_state)"
  obtains f_roots f_challenges roots challenges ys where
    "length f_roots = f_nrounds"
    "length f_challenges = f_nrounds"
    "f_fl = zip f_challenges f_roots"
    "\<And>j. j < f_nrounds \<Longrightarrow> f_roots ! j = value (f_ms ! j)"
    "\<And>j. j < f_nrounds \<Longrightarrow>
      p.next_fri_layer (f_ps ! j) (f_ds ! j) (f_challenges ! j) =
        (f_ps ! Suc j, f_ds ! Suc j, f_ls ! Suc j)"
    "f_final = hd (last f_ls)"
    "length roots = nrounds"
    "length challenges = nrounds"
    "fl = zip challenges roots"
    "\<And>j. j < nrounds \<Longrightarrow> roots ! j = value (ms ! j)"
    "\<And>j. j < nrounds \<Longrightarrow>
      p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    "fr = value f_merkle"
    "as' = as"
    "dg = of_nat (degree (p.cp as p.f_powers))"
    "final = hd (last ls)"
    "PState t = PState s_final"
    "PTranscript t = rev ys"
    "PTranscript prover_state = ys @ PTranscript s_final"
    "replay_state \<le> t"
proof -
  from trace_fri_commit_initial_replay_successor_data[OF trace_fri] obtain f_roots f_challenges where
    f_len_roots: "length f_roots = f_nrounds"
    and f_len_challenges: "length f_challenges = f_nrounds"
    and tr_trace_fri: "PTranscript s_trace_fri = rev f_roots @ PTranscript s2"
    and st_trace_fri: "PState s_trace_fri = foldl concat (PState s2) f_roots"
	    and trace_fri_lookups_state:
	      "\<forall>i < length f_roots.
	        fmlookup (HashMap s_trace_fri)
	          (TraceFriChallenge (PTraceFriCounter s2 + i)
	            (foldl concat (PState s2) (take (Suc i) f_roots))) =
	          Some (f_challenges ! i)"
    and f_roots_aligned_all: "\<forall>j < f_nrounds. f_roots ! j = value (f_ms ! j)"
    and f_successors_all:
      "\<forall>j < f_nrounds.
        p.next_fri_layer (f_ps ! j) (f_ds ! j) (f_challenges ! j) =
          (f_ps ! Suc j, f_ds ! Suc j, f_ls ! Suc j)"
    by blast
  from composition_fri_commit_initial_replay_successor_data[OF fri] obtain roots challenges where
    len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and tr_s6: "PTranscript s6 = rev roots @ PTranscript s5"
    and st_s6: "PState s6 = foldl concat (PState s5) roots"
	    and fri_lookups_s6:
	      "\<forall>i < length roots.
	        fmlookup (HashMap s6)
	          (CompositionFriChallenge
	            (PCompositionFriCounter s5 + i)
	            (foldl concat (PState s5) (take (Suc i) roots))) =
	          Some (challenges ! i)"
    and roots_aligned_all: "\<forall>j < nrounds. roots ! j = value (ms ! j)"
    and successors_all:
      "\<forall>j < nrounds.
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    by blast
  have alpha_data:
    "length as = length spec \<and>
	     s_trace_final \<le> s3 \<and>
		     PState s3 = foldl concat (PState s_trace_final) as \<and>
		     PTranscript s3 = rev as @ PTranscript s_trace_final \<and>
         PCompositionFriCounter s3 = PCompositionFriCounter s_trace_final \<and>
		     (\<forall>i < length as.
		        fmlookup (HashMap s3)
		          (AlphaChallenge (PAlphaCounter s_trace_final + i)
	            (foldl concat (PState s_trace_final) (take i as))) =
	          Some (as ! i))"
    using alpha_mmap_outcome[OF alphas] by simp
  have tail_hash: "s_final \<le> prover_state"
    by (rule ntimes_hash_extends[OF _ tail])
      (rule prover_query_round_hash_extends)
  have trace_fri_final_hash: "s_trace_fri \<le> s_trace_final"
    using send_hash_extends[OF trace_final_send] .
  have s3_s4: "s3 \<le> s4"
    using send_hash_extends[OF send_degree] .
  have s4_s5: "s4 \<le> s5"
    using create_hash_extends[OF create_cp] .
  have s5_s6: "s5 \<le> s6"
    using p.composition_fri_commit_extends[OF fri] .
  have s6_final_hash: "s6 \<le> s_final"
    using send_hash_extends[OF final_send] .
  have trace_fri_prover: "s_trace_fri \<le> prover_state"
    using trace_fri_final_hash alpha_data s3_s4 s4_s5 s5_s6 s6_final_hash tail_hash
    by (meson p.hash_ext_trans)
  have s3_prover: "s3 \<le> prover_state"
    using s3_s4 s4_s5 s5_s6 s6_final_hash tail_hash by (meson p.hash_ext_trans)
  have s6_prover: "s6 \<le> prover_state"
    using s6_final_hash tail_hash by (rule p.hash_ext_trans)
  have final_tail_tr: "transcript_extends prover_state s_final"
    by (rule ntimes_transcript_extends[OF _ tail])
      (rule prover_query_round_transcript_extends)
  from final_tail_tr obtain ys where
    tr_prover: "PTranscript prover_state = ys @ PTranscript s_final"
    unfolding transcript_extends_def by auto
  have tr_s1: "PTranscript s1 = []"
    using create_preserves_transcript[OF create_f]
    unfolding init_state_def by simp
  have send_f_res:
    "s2 = s1\<lparr>
      PState := concat (PState s1) (value f_merkle),
      PTranscript := value f_merkle # PTranscript s1\<rparr>"
    using p.send_outcome[OF send_f] .
  have trace_final_res:
    "s_trace_final = s_trace_fri\<lparr>
      PState := concat (PState s_trace_fri) (hd (last f_ls)),
      PTranscript := hd (last f_ls) # PTranscript s_trace_fri\<rparr>"
    using p.send_outcome[OF trace_final_send] .
  have send_degree_res:
    "s4 = s3\<lparr>
      PState := concat (PState s3) (of_nat (degree cp')),
      PTranscript := of_nat (degree cp') # PTranscript s3\<rparr>"
    using p.send_outcome[OF send_degree] .
  have tr_s5: "PTranscript s5 = PTranscript s4"
    using create_preserves_transcript[OF create_cp] .
  have final_send_res:
    "s_final = s6\<lparr>
      PState := concat (PState s6) (hd (last ls)),
      PTranscript := hd (last ls) # PTranscript s6\<rparr>"
    using p.send_outcome[OF final_send] .
  have replay_prefix:
    "PTranscript replay_state =
      value f_merkle # f_roots @ [hd (last f_ls)] @
        as @ [of_nat (degree (p.cp as p.f_powers))] @ roots @ [hd (last ls)] @ rev ys"
    using replay tr_prover final_send_res tr_s6 tr_s5 send_degree_res alpha_data
      trace_final_res tr_trace_fri send_f_res tr_s1 cp'_def
    unfolding verifier_replay_state_def by simp
  have st_s1: "PState s1 = 0"
    using create_preserves_state[OF create_f]
    unfolding init_state_def by simp
  have st_trace_final:
    "PState s_trace_final =
      concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
        (hd (last f_ls))"
    using st_s1 send_f_res st_trace_fri trace_final_res replay
    unfolding verifier_replay_state_def by simp
  have st_s5:
    "PState s5 =
      concat
        (foldl concat
          (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
            (hd (last f_ls)))
          as)
        (of_nat (degree (p.cp as p.f_powers)))"
    using st_trace_final alpha_data send_degree_res create_preserves_state[OF create_cp] cp'_def
    by simp
  have trace_counter_s1_zero: "PTraceFriCounter s1 = 0"
    using p.create_preserves_channel(3)[OF create_f]
    unfolding init_state_def by simp
  have trace_counter_s2_zero: "PTraceFriCounter s2 = 0"
    using send_f_res trace_counter_s1_zero by simp
  have alpha_counter_s1_zero: "PAlphaCounter s1 = 0"
    using p.create_preserves_channel(5)[OF create_f]
    unfolding init_state_def by simp
  have alpha_counter_s2_zero: "PAlphaCounter s2 = 0"
    using send_f_res alpha_counter_s1_zero by simp
  have alpha_counter_trace_fri_zero: "PAlphaCounter s_trace_fri = 0"
    using trace_fri_commit_preserves_alpha_counter[OF trace_fri]
      alpha_counter_s2_zero by simp
  have alpha_counter_trace_final_zero: "PAlphaCounter s_trace_final = 0"
    using trace_final_res alpha_counter_trace_fri_zero by simp
  have comp_counter_s1_zero: "PCompositionFriCounter s1 = 0"
    using p.create_preserves_channel(4)[OF create_f]
    unfolding init_state_def by simp
  have comp_counter_s2_zero: "PCompositionFriCounter s2 = 0"
    using send_f_res comp_counter_s1_zero by simp
  have comp_counter_trace_fri_zero: "PCompositionFriCounter s_trace_fri = 0"
    using trace_fri_commit_preserves_composition_counter[OF trace_fri]
      comp_counter_s2_zero by simp
  have comp_counter_trace_final_zero:
    "PCompositionFriCounter s_trace_final = 0"
    using trace_final_res comp_counter_trace_fri_zero by simp
  have comp_counter_s3_zero: "PCompositionFriCounter s3 = 0"
    using alpha_data comp_counter_trace_final_zero by simp
  have comp_counter_s4_zero: "PCompositionFriCounter s4 = 0"
    using send_degree_res comp_counter_s3_zero by simp
  have comp_counter_s5_zero: "PCompositionFriCounter s5 = 0"
    using p.create_preserves_channel(4)[OF create_cp] comp_counter_s4_zero
    by simp
  have f_fri_lookups:
    "\<forall>i < length f_roots.
      fmlookup (HashMap replay_state)
        (TraceFriChallenge (PTraceFriCounter replay_state + i) (foldl concat
          (concat (PState replay_state) (value f_merkle))
          (take (Suc i) f_roots))) =
        Some (f_challenges ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length f_roots"
    have lookup_trace:
	      "fmlookup (HashMap s_trace_fri)
	        (TraceFriChallenge (PTraceFriCounter s2 + i)
	          (foldl concat (PState s2) (take (Suc i) f_roots))) =
	        Some (f_challenges ! i)"
      using trace_fri_lookups_state i_bound by simp
    have lookup_prover:
	      "fmlookup (HashMap prover_state)
	        (TraceFriChallenge (PTraceFriCounter s2 + i)
	          (foldl concat (PState s2) (take (Suc i) f_roots))) =
	        Some (f_challenges ! i)"
      using p.hash_extension_lookup[OF lookup_trace trace_fri_prover] .
    show "fmlookup (HashMap replay_state)
      (TraceFriChallenge (PTraceFriCounter replay_state + i) (foldl concat
        (concat (PState replay_state) (value f_merkle))
        (take (Suc i) f_roots))) =
      Some (f_challenges ! i)"
      using lookup_prover send_f_res st_s1 replay trace_counter_s2_zero
      unfolding verifier_replay_state_def by simp
  qed
  have alpha_lookups:
    "\<forall>i < length as.
      fmlookup (HashMap replay_state)
        (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat
          (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
            (hd (last f_ls)))
          (take i as))) =
        Some (as ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length as"
    have alpha_lookups_s3:
	      "\<forall>i < length as.
	        fmlookup (HashMap s3)
	          (AlphaChallenge (PAlphaCounter s_trace_final + i)
	            (foldl concat (PState s_trace_final) (take i as))) =
	          Some (as ! i)"
      using alpha_data by simp
    have lookup_s3:
	      "fmlookup (HashMap s3)
	        (AlphaChallenge (PAlphaCounter s_trace_final + i)
	          (foldl concat (PState s_trace_final) (take i as))) =
	        Some (as ! i)"
      using alpha_lookups_s3 i_bound by simp
    have lookup_prover:
	      "fmlookup (HashMap prover_state)
	        (AlphaChallenge (PAlphaCounter s_trace_final + i)
	          (foldl concat (PState s_trace_final) (take i as))) =
	        Some (as ! i)"
      using p.hash_extension_lookup[OF lookup_s3 s3_prover] .
    show "fmlookup (HashMap replay_state)
      (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat
        (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
          (hd (last f_ls)))
        (take i as))) =
      Some (as ! i)"
      using lookup_prover st_trace_final replay alpha_counter_trace_final_zero
      unfolding verifier_replay_state_def by simp
  qed
  have fri_lookups:
    "\<forall>i < length roots.
      fmlookup (HashMap replay_state)
        (CompositionFriChallenge (PCompositionFriCounter replay_state + i) (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
                (hd (last f_ls)))
              as)
            (of_nat (degree (p.cp as p.f_powers))))
          (take (Suc i) roots))) =
        Some (challenges ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length roots"
    have lookup_s6:
	      "fmlookup (HashMap s6)
	        (CompositionFriChallenge
	          (PCompositionFriCounter s5 + i)
	          (foldl concat (PState s5) (take (Suc i) roots))) =
	        Some (challenges ! i)"
      using fri_lookups_s6 i_bound by simp
    have lookup_prover:
	      "fmlookup (HashMap prover_state)
	        (CompositionFriChallenge
	          (PCompositionFriCounter s5 + i)
	          (foldl concat (PState s5) (take (Suc i) roots))) =
	        Some (challenges ! i)"
      using p.hash_extension_lookup[OF lookup_s6 s6_prover] .
    show "fmlookup (HashMap replay_state)
      (CompositionFriChallenge (PCompositionFriCounter replay_state + i) (foldl concat
        (concat
          (foldl concat
            (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
              (hd (last f_ls)))
            as)
          (of_nat (degree (p.cp as p.f_powers))))
        (take (Suc i) roots))) =
      Some (challenges ! i)"
      using lookup_prover st_s5 replay comp_counter_s5_zero
      unfolding verifier_replay_state_def by simp
  qed
  have f_roots_rounds: "length f_roots = ceil_log clength"
    using f_len_roots f_nrounds_def by simp
  have f_len_challenges_roots: "length f_challenges = length f_roots"
    using f_len_challenges f_len_roots by simp
  have roots_rounds:
    "length roots = ceil_log (degree (p.cp as p.f_powers) + 1)"
    using len_roots nrounds_def cp'_def by simp
  have len_challenges_roots: "length challenges = length roots"
    using len_challenges len_roots by simp
  have prefix_res:
    "fr = value f_merkle \<and>
     f_fl = zip f_challenges f_roots \<and>
     f_final = hd (last f_ls) \<and>
     as' = as \<and>
     dg = of_nat (degree (p.cp as p.f_powers)) \<and>
     fl = zip challenges roots \<and>
     final = hd (last ls) \<and>
     PState t =
       concat
         (foldl concat
           (concat
             (foldl concat
               (concat (foldl concat (concat (PState replay_state) (value f_merkle)) f_roots)
                 (hd (last f_ls)))
               as)
             (of_nat (degree (p.cp as p.f_powers))))
           roots)
         (hd (last ls)) \<and>
     PTranscript t = rev ys \<and>
     replay_state \<le> t"
    by (rule honest_trace_root_alpha_degree_fri_final_dynamic_prefix_outcome[
        OF htv conjunct1[OF alpha_data] f_len_challenges_roots f_roots_rounds
          len_challenges_roots roots_rounds replay_prefix f_fri_lookups
          alpha_lookups fri_lookups outcome])
  have st_t_final: "PState t = PState s_final"
    using prefix_res st_s5 st_s6 final_send_res by simp
  show ?thesis
    by (rule that[
        OF f_len_roots f_len_challenges _ _ _ _ len_roots len_challenges _ _ _
          _ _ _ _ st_t_final _ tr_prover _])
      (use prefix_res f_roots_aligned_all f_successors_all roots_aligned_all successors_all in simp_all)
qed

lemma honest_root_alpha_degree_from_prover_no_failure:
  assumes htv: "honest_trace_valid"
      and create_f:
        "Some (f_merkle, s1) \<in>
          set_dist (execute (p.create p.f_eval) init_state)"
      and created_f: "p.created_tree p.f_eval f_merkle s1"
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
        return (fr, as', dg)
      }) replay_state))"
proof -
  have root_alpha_tr:
    "length as = length spec \<and>
     PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
    by (rule prover_root_alpha_degree_transcript[
        OF create_f send_f alphas cp'_def send_degree])
  have later_tr: "transcript_extends prover_state s4"
    by (rule prover_later_phases_transcript_extends[
        OF create_cp fri final_send random_idx query_decommit fri_decommit prover_state_eq])
  from verifier_replay_root_alpha_degree_prefix[
      OF conjunct2[OF root_alpha_tr] later_tr replay]
  obtain rest where prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree cp')] @ rest"
    by blast
  have prefix_cp:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @ rest"
    using prefix cp'_def by simp
  have later_hash: "s3 \<le> prover_state"
    by (rule prover_later_phases_hash_extends[
        OF send_degree create_cp fri final_send random_idx query_decommit fri_decommit prover_state_eq])
  have lookups:
    "\<forall>i < length as.
      fmlookup (HashMap replay_state)
        (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
        Some (as ! i)"
    by (rule prover_alpha_lookups_in_replay_state[
        OF create_f send_f alphas later_hash replay])
  show ?thesis
    by (rule honest_root_alpha_degree_prefix_no_failure[
        OF htv conjunct1[OF root_alpha_tr] prefix_cp lookups])
qed

lemma honest_root_alpha_degree_from_prover_outcome:
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
      "Some ((fr, as', dg), t) \<in> set_dist (execute
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
          return (fr, as', dg)
        }) replay_state)"
  shows
    "fr = value f_merkle \<and>
     as' = as \<and>
     dg = of_nat (degree (p.cp as p.f_powers)) \<and>
     replay_state \<le> t"
proof -
  have root_alpha_tr:
    "length as = length spec \<and>
     PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
    by (rule prover_root_alpha_degree_transcript[
        OF create_f send_f alphas cp'_def send_degree])
  have later_tr: "transcript_extends prover_state s4"
    by (rule prover_later_phases_transcript_extends[
        OF create_cp fri final_send random_idx query_decommit fri_decommit prover_state_eq])
  from verifier_replay_root_alpha_degree_prefix[
      OF conjunct2[OF root_alpha_tr] later_tr replay]
  obtain rest where prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree cp')] @ rest"
    by blast
  have prefix_cp:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @ rest"
    using prefix cp'_def by simp
  have later_hash: "s3 \<le> prover_state"
    by (rule prover_later_phases_hash_extends[
        OF send_degree create_cp fri final_send random_idx query_decommit fri_decommit prover_state_eq])
  have lookups:
    "\<forall>i < length as.
      fmlookup (HashMap replay_state)
        (AlphaChallenge (PAlphaCounter replay_state + i) (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
        Some (as ! i)"
    by (rule prover_alpha_lookups_in_replay_state[
        OF create_f send_f alphas later_hash replay])
  have out:
    "fr = value f_merkle \<and>
     as' = as \<and>
     dg = of_nat (degree (p.cp as p.f_powers)) \<and>
     PState t =
       concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
         (of_nat (degree (p.cp as p.f_powers))) \<and>
     PTranscript t = rest \<and>
     replay_state \<le> t"
    by (rule honest_root_alpha_degree_prefix_outcome[
        OF htv conjunct1[OF root_alpha_tr] prefix_cp lookups outcome])
  then show ?thesis by simp
qed

lemma honest_root_alpha_degree_fri_from_prover_no_failure:
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
        return (fr, as', dg, fl)
      }) replay_state))"
proof -
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
  have after_tr: "transcript_extends prover_state s6"
    by (rule prover_after_fri_transcript_extends[
        OF final_send random_idx query_decommit fri_decommit prover_state_eq])
  from after_tr obtain xs where
    tr_prover: "PTranscript prover_state = xs @ PTranscript s6"
    unfolding transcript_extends_def by auto
  have tr_s5: "PTranscript s5 = PTranscript s4"
    using create_preserves_transcript[OF create_cp] .
  have replay_prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @ roots @ rev xs"
    using replay tr_prover tr_s6 tr_s5 root_alpha_tr cp'_def
    unfolding verifier_replay_state_def by simp
  have st_s1: "PState s1 = 0"
    using create_preserves_state[OF create_f]
    unfolding init_state_def by simp
  have send_f_res:
    "s2 = s1\<lparr>
      PState := concat (PState s1) (value f_merkle),
      PTranscript := value f_merkle # PTranscript s1\<rparr>"
    using p.send_outcome[OF send_f] .
  have alpha_data:
    "PState s3 = foldl concat (PState s2) as"
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
  have nf_roots:
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
        fl \<leftarrow> ntimes v.receive_fri_commits (length roots);
        return (fr, as', dg, fl)
      }) replay_state))"
    by (rule honest_root_alpha_degree_fri_prefix_no_failure[
        OF htv conjunct1[OF root_alpha_tr] _ replay_prefix alpha_lookups fri_lookups])
      (use len_roots len_challenges in simp_all)
  show ?thesis
    using nf_roots len_roots by simp
qed

lemma honest_root_alpha_degree_fri_from_prover_tail_no_failure:
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
    and tail:
      "Some (prover_result, prover_state) \<in>
        set_dist (execute (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds) s_final)"
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
        return (fr, as', dg, fl)
      }) replay_state))"
proof -
  have root_alpha_tr:
    "length as = length spec \<and>
     PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
    by (rule prover_root_alpha_degree_transcript[
        OF create_f send_f alphas cp'_def send_degree])
  have tail_hash: "s_final \<le> prover_state"
    by (rule ntimes_hash_extends[OF _ tail])
      (rule prover_query_round_hash_extends)
  have s3_s4: "s3 \<le> s4"
    using send_hash_extends[OF send_degree] .
  have s4_s5: "s4 \<le> s5"
    using create_hash_extends[OF create_cp] .
  have s5_s6: "s5 \<le> s6"
    using honest_fri_commit_extends[OF fri] .
  have s6_final_hash: "s6 \<le> s_final"
    using send_hash_extends[OF final_send] .
  have later_hash: "s3 \<le> prover_state"
    using s3_s4 s4_s5 s5_s6 s6_final_hash tail_hash by (meson p.hash_ext_trans)
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
  have s6_final_tr: "transcript_extends s_final s6"
    using send_transcript_extends[OF final_send] .
  have final_tail_tr: "transcript_extends prover_state s_final"
    by (rule ntimes_transcript_extends[OF _ tail])
      (rule prover_query_round_transcript_extends)
  have after_tr: "transcript_extends prover_state s6"
    using s6_final_tr final_tail_tr by (meson transcript_extends_trans)
  from after_tr obtain xs where
    tr_prover: "PTranscript prover_state = xs @ PTranscript s6"
    unfolding transcript_extends_def by auto
  have tr_s5: "PTranscript s5 = PTranscript s4"
    using create_preserves_transcript[OF create_cp] .
  have replay_prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @ roots @ rev xs"
    using replay tr_prover tr_s6 tr_s5 root_alpha_tr cp'_def
    unfolding verifier_replay_state_def by simp
  have st_s1: "PState s1 = 0"
    using create_preserves_state[OF create_f]
    unfolding init_state_def by simp
  have send_f_res:
    "s2 = s1\<lparr>
      PState := concat (PState s1) (value f_merkle),
      PTranscript := value f_merkle # PTranscript s1\<rparr>"
    using p.send_outcome[OF send_f] .
  have alpha_data:
    "PState s3 = foldl concat (PState s2) as"
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
    using s6_final_hash tail_hash by (rule p.hash_ext_trans)
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
  have nf_roots:
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
        fl \<leftarrow> ntimes v.receive_fri_commits (length roots);
        return (fr, as', dg, fl)
      }) replay_state))"
    by (rule honest_root_alpha_degree_fri_prefix_no_failure[
        OF htv conjunct1[OF root_alpha_tr] _ replay_prefix alpha_lookups fri_lookups])
      (use len_roots len_challenges in simp_all)
  show ?thesis
    using nf_roots len_roots by simp
qed

lemma honest_root_alpha_degree_fri_final_dynamic_from_prover_tail_no_failure:
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
    and tail:
      "Some (prover_result, prover_state) \<in>
        set_dist (execute (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds) s_final)"
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
        return (fr, as', dg, fl, final)
      }) replay_state))"
proof -
  have root_alpha_tr:
    "length as = length spec \<and>
     PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
    by (rule prover_root_alpha_degree_transcript[
        OF create_f send_f alphas cp'_def send_degree])
  have tail_hash: "s_final \<le> prover_state"
    by (rule ntimes_hash_extends[OF _ tail])
      (rule prover_query_round_hash_extends)
  have s3_s4: "s3 \<le> s4"
    using send_hash_extends[OF send_degree] .
  have s4_s5: "s4 \<le> s5"
    using create_hash_extends[OF create_cp] .
  have s5_s6: "s5 \<le> s6"
    using honest_fri_commit_extends[OF fri] .
  have s6_final_hash: "s6 \<le> s_final"
    using send_hash_extends[OF final_send] .
  have later_hash: "s3 \<le> prover_state"
    using s3_s4 s4_s5 s5_s6 s6_final_hash tail_hash by (meson p.hash_ext_trans)
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
    and fri_lookups_s6:
      "\<forall>i < length roots.
        fmlookup (HashMap s6) (FiatShamirChallenge (foldl concat (PState s5) (take (Suc i) roots))) =
          Some (challenges ! i)"
    by blast
  have final_tail_tr: "transcript_extends prover_state s_final"
    by (rule ntimes_transcript_extends[OF _ tail])
      (rule prover_query_round_transcript_extends)
  from final_tail_tr obtain ys where
    tr_prover: "PTranscript prover_state = ys @ PTranscript s_final"
    unfolding transcript_extends_def by auto
  have tr_s5: "PTranscript s5 = PTranscript s4"
    using create_preserves_transcript[OF create_cp] .
  have final_send_res:
    "s_final = s6\<lparr>
      PState := concat (PState s6) (hd (last ls)),
      PTranscript := hd (last ls) # PTranscript s6\<rparr>"
    using p.send_outcome[OF final_send] .
  have replay_prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
        roots @ [hd (last ls)] @ rev ys"
    using replay tr_prover final_send_res tr_s6 tr_s5 root_alpha_tr cp'_def
    unfolding verifier_replay_state_def by simp
  have st_s1: "PState s1 = 0"
    using create_preserves_state[OF create_f]
    unfolding init_state_def by simp
  have send_f_res:
    "s2 = s1\<lparr>
      PState := concat (PState s1) (value f_merkle),
      PTranscript := value f_merkle # PTranscript s1\<rparr>"
    using p.send_outcome[OF send_f] .
  have alpha_data:
    "PState s3 = foldl concat (PState s2) as"
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
    using s6_final_hash tail_hash by (rule p.hash_ext_trans)
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
  have roots_rounds:
    "length roots = ceil_log (degree (p.cp as p.f_powers) + 1)"
    using len_roots nrounds_def cp'_def by simp
  have len_challenges_roots: "length challenges = length roots"
    using len_challenges len_roots by simp
	  show ?thesis
	    by (rule honest_root_alpha_degree_fri_final_dynamic_prefix_no_failure[
	        OF htv conjunct1[OF root_alpha_tr] len_challenges_roots roots_rounds
	          replay_prefix alpha_lookups fri_lookups])
	qed

	lemma honest_root_alpha_degree_fri_final_dynamic_from_prover_tail_outcome:
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
	    and tail:
	      "Some (prover_result, prover_state) \<in>
	        set_dist (execute (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds) s_final)"
	    and replay: "replay_state = verifier_replay_state prover_state"
	    and outcome:
	      "Some ((fr, as', dg, fl, final), t) \<in> set_dist (execute
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
	          return (fr, as', dg, fl, final)
	        }) replay_state)"
	  obtains roots challenges ys where
	    "length roots = nrounds"
	    "length challenges = nrounds"
	    "fl = zip challenges roots"
	    "\<And>j. j < nrounds \<Longrightarrow> roots ! j = value (ms ! j)"
	    "\<And>j. j < nrounds \<Longrightarrow>
	      p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
	        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
	    "fr = value f_merkle"
	    "as' = as"
	    "dg = of_nat (degree (p.cp as p.f_powers))"
	    "final = hd (last ls)"
	    "PState t = PState s_final"
	    "PTranscript t = rev ys"
	    "PTranscript prover_state = ys @ PTranscript s_final"
	    "replay_state \<le> t"
	proof -
	  have root_alpha_tr:
	    "length as = length spec \<and>
	     PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
	    by (rule prover_root_alpha_degree_transcript[
	        OF create_f send_f alphas cp'_def send_degree])
	  have tail_hash: "s_final \<le> prover_state"
	    by (rule ntimes_hash_extends[OF _ tail])
	      (rule prover_query_round_hash_extends)
	  have s3_s4: "s3 \<le> s4"
	    using send_hash_extends[OF send_degree] .
	  have s4_s5: "s4 \<le> s5"
	    using create_hash_extends[OF create_cp] .
	  have s5_s6: "s5 \<le> s6"
	    using honest_fri_commit_extends[OF fri] .
	  have s6_final_hash: "s6 \<le> s_final"
	    using send_hash_extends[OF final_send] .
	  have later_hash: "s3 \<le> prover_state"
	    using s3_s4 s4_s5 s5_s6 s6_final_hash tail_hash by (meson p.hash_ext_trans)
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
	    and s5_s6': "s5 \<le> s6"
	    and fri_lookups_s6:
	      "\<forall>i < length roots.
	        fmlookup (HashMap s6) (FiatShamirChallenge (foldl concat (PState s5) (take (Suc i) roots))) =
	          Some (challenges ! i)"
	    and roots_aligned_all: "\<forall>j < nrounds. roots ! j = value (ms ! j)"
	    and successors_all:
	      "\<forall>j < nrounds.
	        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
	          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
	    by blast
	  have roots_aligned:
	    "\<And>j. j < nrounds \<Longrightarrow> roots ! j = value (ms ! j)"
	    using roots_aligned_all by simp
	  have successors:
	    "\<And>j. j < nrounds \<Longrightarrow>
	      p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
	        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
	    using successors_all by simp
	  have final_tail_tr: "transcript_extends prover_state s_final"
	    by (rule ntimes_transcript_extends[OF _ tail])
	      (rule prover_query_round_transcript_extends)
	  from final_tail_tr obtain ys where
	    tr_prover: "PTranscript prover_state = ys @ PTranscript s_final"
	    unfolding transcript_extends_def by auto
	  have tr_s5: "PTranscript s5 = PTranscript s4"
	    using create_preserves_transcript[OF create_cp] .
	  have final_send_res:
	    "s_final = s6\<lparr>
	      PState := concat (PState s6) (hd (last ls)),
	      PTranscript := hd (last ls) # PTranscript s6\<rparr>"
	    using p.send_outcome[OF final_send] .
	  have replay_prefix:
	    "PTranscript replay_state =
	      value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
	        roots @ [hd (last ls)] @ rev ys"
	    using replay tr_prover final_send_res tr_s6 tr_s5 root_alpha_tr cp'_def
	    unfolding verifier_replay_state_def by simp
	  have st_s1: "PState s1 = 0"
	    using create_preserves_state[OF create_f]
	    unfolding init_state_def by simp
	  have send_f_res:
	    "s2 = s1\<lparr>
	      PState := concat (PState s1) (value f_merkle),
	      PTranscript := value f_merkle # PTranscript s1\<rparr>"
	    using p.send_outcome[OF send_f] .
	  have alpha_data:
	    "PState s3 = foldl concat (PState s2) as"
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
	    using s6_final_hash tail_hash by (rule p.hash_ext_trans)
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
	  have roots_rounds:
	    "length roots = ceil_log (degree (p.cp as p.f_powers) + 1)"
	    using len_roots nrounds_def cp'_def by simp
	  have len_challenges_roots: "length challenges = length roots"
	    using len_challenges len_roots by simp
	  have prefix_res:
	    "fr = value f_merkle \<and>
	     as' = as \<and>
	     dg = of_nat (degree (p.cp as p.f_powers)) \<and>
	     fl = zip challenges roots \<and>
	     final = hd (last ls) \<and>
	     PState t =
	       concat
	         (foldl concat
	           (concat (foldl concat (concat (PState replay_state) (value f_merkle)) as)
	             (of_nat (degree (p.cp as p.f_powers))))
	           roots)
	         (hd (last ls)) \<and>
	     PTranscript t = rev ys \<and>
	     replay_state \<le> t"
	    by (rule honest_root_alpha_degree_fri_final_dynamic_prefix_outcome[
	        OF htv conjunct1[OF root_alpha_tr] len_challenges_roots roots_rounds
	          replay_prefix alpha_lookups fri_lookups outcome])
	  have st_t_final: "PState t = PState s_final"
	    using prefix_res st_s5 st_s6 final_send_res by simp
	  show ?thesis
	    by (rule that[
	        OF len_roots len_challenges _ roots_aligned successors _ _ _ _
	          st_t_final _ tr_prover _])
	      (use prefix_res in simp_all)
	qed

lemma honest_root_alpha_degree_fri_final_from_prover_no_failure:
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
        return (fr, as', dg, fl, final)
      }) replay_state))"
proof -
  have root_alpha_tr:
    "length as = length spec \<and>
     PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
    by (rule prover_root_alpha_degree_transcript[
        OF create_f send_f alphas cp'_def send_degree])
  have later_hash: "s3 \<le> prover_state"
    by (rule prover_later_phases_hash_extends[
        OF send_degree create_cp fri final_send random_idx
          query_decommit fri_decommit prover_state_eq])
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
  have final_tail_tr: "transcript_extends prover_state s_final"
  proof -
    have final_s7: "transcript_extends s7 s_final"
      using receive_query_index_challenge_transcript_extends[OF random_idx] .
    have s7_s8: "transcript_extends s8 s7"
      by (rule mmap_transcript_extends[OF query_decommit])
        (rule decommit_on_query_step_transcript_extends)
    have s8_s9: "transcript_extends s9 s8"
      by (rule mfold_transcript_extends[OF fri_decommit])
        (rule decommit_on_fri_layers_step_transcript_extends)
    have s9_prover: "transcript_extends prover_state s9"
      using prover_state_eq by simp
    show ?thesis
      using final_s7 s7_s8 s8_s9 s9_prover by (meson transcript_extends_trans)
  qed
  from final_tail_tr obtain ys where
    tr_prover: "PTranscript prover_state = ys @ PTranscript s_final"
    unfolding transcript_extends_def by auto
  have tr_s5: "PTranscript s5 = PTranscript s4"
    using create_preserves_transcript[OF create_cp] .
  have final_send_res:
    "s_final = s6\<lparr>
      PState := concat (PState s6) (hd (last ls)),
      PTranscript := hd (last ls) # PTranscript s6\<rparr>"
    using p.send_outcome[OF final_send] .
  have replay_prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
        roots @ [hd (last ls)] @ rev ys"
    using replay tr_prover final_send_res tr_s6 tr_s5 root_alpha_tr cp'_def
    unfolding verifier_replay_state_def by simp
  have st_s1: "PState s1 = 0"
    using create_preserves_state[OF create_f]
    unfolding init_state_def by simp
  have send_f_res:
    "s2 = s1\<lparr>
      PState := concat (PState s1) (value f_merkle),
      PTranscript := value f_merkle # PTranscript s1\<rparr>"
    using p.send_outcome[OF send_f] .
  have alpha_data:
    "PState s3 = foldl concat (PState s2) as"
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
  have len_challenges_roots: "length challenges = length roots"
    using len_challenges len_roots by simp
  have nf_roots:
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
        fl \<leftarrow> ntimes v.receive_fri_commits (length roots);
        final \<leftarrow> p.read;
        return (fr, as', dg, fl, final)
      }) replay_state))"
    by (rule honest_root_alpha_degree_fri_final_prefix_no_failure[
        OF htv conjunct1[OF root_alpha_tr] len_challenges_roots
          replay_prefix alpha_lookups fri_lookups])
  show ?thesis
    using nf_roots len_roots by simp
qed

lemma honest_root_alpha_degree_fri_final_dynamic_from_prover_no_failure:
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
        return (fr, as', dg, fl, final)
      }) replay_state))"
proof -
  have root_alpha_tr:
    "length as = length spec \<and>
     PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
    by (rule prover_root_alpha_degree_transcript[
        OF create_f send_f alphas cp'_def send_degree])
  have later_hash: "s3 \<le> prover_state"
    by (rule prover_later_phases_hash_extends[
        OF send_degree create_cp fri final_send random_idx
          query_decommit fri_decommit prover_state_eq])
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
  have final_tail_tr: "transcript_extends prover_state s_final"
  proof -
    have final_s7: "transcript_extends s7 s_final"
      using receive_query_index_challenge_transcript_extends[OF random_idx] .
    have s7_s8: "transcript_extends s8 s7"
      by (rule mmap_transcript_extends[OF query_decommit])
        (rule decommit_on_query_step_transcript_extends)
    have s8_s9: "transcript_extends s9 s8"
      by (rule mfold_transcript_extends[OF fri_decommit])
        (rule decommit_on_fri_layers_step_transcript_extends)
    have s9_prover: "transcript_extends prover_state s9"
      using prover_state_eq by simp
    show ?thesis
      using final_s7 s7_s8 s8_s9 s9_prover by (meson transcript_extends_trans)
  qed
  from final_tail_tr obtain ys where
    tr_prover: "PTranscript prover_state = ys @ PTranscript s_final"
    unfolding transcript_extends_def by auto
  have tr_s5: "PTranscript s5 = PTranscript s4"
    using create_preserves_transcript[OF create_cp] .
  have final_send_res:
    "s_final = s6\<lparr>
      PState := concat (PState s6) (hd (last ls)),
      PTranscript := hd (last ls) # PTranscript s6\<rparr>"
    using p.send_outcome[OF final_send] .
  have replay_prefix:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
        roots @ [hd (last ls)] @ rev ys"
    using replay tr_prover final_send_res tr_s6 tr_s5 root_alpha_tr cp'_def
    unfolding verifier_replay_state_def by simp
  have st_s1: "PState s1 = 0"
    using create_preserves_state[OF create_f]
    unfolding init_state_def by simp
  have send_f_res:
    "s2 = s1\<lparr>
      PState := concat (PState s1) (value f_merkle),
      PTranscript := value f_merkle # PTranscript s1\<rparr>"
    using p.send_outcome[OF send_f] .
  have alpha_data:
    "PState s3 = foldl concat (PState s2) as"
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
  have roots_rounds:
    "length roots = ceil_log (degree (p.cp as p.f_powers) + 1)"
    using len_roots nrounds_def cp'_def by simp
  have len_challenges_roots: "length challenges = length roots"
    using len_challenges len_roots by simp
  show ?thesis
    by (rule honest_root_alpha_degree_fri_final_dynamic_prefix_no_failure[
        OF htv conjunct1[OF root_alpha_tr] len_challenges_roots roots_rounds
          replay_prefix alpha_lookups fri_lookups])
qed

end

end
