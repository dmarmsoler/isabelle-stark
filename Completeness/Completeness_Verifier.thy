(*  Title:      Stark/Completeness_Verifier.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Completeness_Verifier
  imports Completeness_FRI
begin

section \<open>Final Completeness Proof\<close>

text \<open>Final honest verifier query-round replay and completeness theorem.\<close>

context verification
begin

lemma honest_fri_decommitments_mfold_no_failure:
  assumes fri:
    "fri_commit_outcome n cp p.eval_domain l0 m0 ps ds ls ms s5 s6"
    and len_ps: "length ps = Suc n"
    and len_ds: "length ds = Suc n"
    and len_ls: "length ls = Suc n"
    and len_ms: "length ms = Suc n"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and created:
      "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
        p.created_tree (ls ! i) (ms ! i) s6"
    and init_len: "length l0 = 2 ^ N"
    and init_domain: "2 ^ N = clength * scale"
    and n_le_N: "n \<le> N"
    and len_roots: "length roots = n"
    and len_challenges: "length challenges = n"
    and roots_aligned: "\<And>j. j < n \<Longrightarrow> roots ! j = value (ms ! j)"
    and successors:
      "\<And>j. j < n \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and idx_bound: "idx < length (ls ! 0)"
    and x0_eq: "x0 = ls ! 0 ! idx"
    and len0_eq: "len0 = length (ls ! 0)"
    and start_tr:
      "PTranscript start = fri_decommitment_transcript idx (butlast (zip ls ms)) @ rest"
    and start_ext: "s6 \<le> start"
  shows
    "None \<notin> dom (dist (execute
      (mfold (idx, x0, len0, 1) (v.receive_query_commits (zip challenges roots)))
      start))"
proof -
  let ?fl =
    "v.receive_query_commits (zip challenges roots) ::
      ((nat \<times> 'f \<times> nat \<times> nat) \<Rightarrow>
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) list"
  let ?bl = "butlast (zip ls ms)"
  define I where
    "I = (\<lambda>(j::nat) (a::nat \<times> 'f \<times> nat \<times> nat)
        (s::'f protocol_channel).
      (case a of (i, x, len, pw) \<Rightarrow>
        i = idx mod length (ls ! j) \<and>
        x = ls ! j ! i \<and>
        len = length (ls ! j) \<and>
        pw = 2 ^ j \<and>
        PTranscript s = fri_decommitment_transcript i (drop j ?bl) @ rest \<and>
        s6 \<le> s))"
  have fl_len: "length ?fl = n"
    using len_roots len_challenges
    unfolding v.receive_query_commits_def by simp
  have init_I: "I 0 (idx, x0, len0, 1) start"
    unfolding I_def
    using idx_bound x0_eq len0_eq start_tr start_ext by simp
  have step_nf:
    "\<And>j m a st. j < length ?fl \<Longrightarrow>
      m = ?fl ! j \<Longrightarrow> I j a st \<Longrightarrow>
      None \<notin> dom (dist (execute (m a) st))"
  proof -
    fix j m a st
    assume j_lt_fl: "j < length ?fl"
      and m_eq: "m = ?fl ! j"
      and inv: "I j a st"
    have j_lt: "j < n"
      using j_lt_fl fl_len by presburger
    obtain i x len pw where a_eq: "a = (i, x, len, pw)"
      by (cases a) auto
    have invD:
      "i = idx mod length (ls ! j)"
      "x = ls ! j ! i"
      "len = length (ls ! j)"
      "pw = 2 ^ j"
      "PTranscript st = fri_decommitment_transcript i (drop j ?bl) @ rest"
      "s6 \<le> st"
      using inv unfolding I_def a_eq by simp_all
    have j_le: "j \<le> n"
      using j_lt by simp
    have len_exact:
      "length (ls ! j) = 2 ^ (N - j)"
      by (rule fri_commit_outcome_initial_layer_length_power[
          OF fri layers init_len n_le_N j_le])
    have j_lt_N: "j < N"
      using j_lt n_le_N by linarith
    have diff_suc: "N - j = Suc (N - Suc j)"
      using j_lt_N by simp
    have len_pow_suc:
      "length (ls ! j) = 2 ^ Suc (N - Suc j)"
      using len_exact diff_suc by simp
    have len_pos: "0 < length (ls ! j)"
      using len_pow_suc by simp
    have i_bound: "i < len"
      using invD len_pos by simp
    have drop_eq:
      "drop j ?bl = (ls ! j, ms ! j) # drop (Suc j) ?bl"
      by (rule butlast_zip_suc_drop_nth[OF len_ls len_ms j_lt])
    have tr_layer:
      "st =
        st\<lparr>PTranscript :=
          fri_layer_decommitment_transcript (ls ! j) (ms ! j) i len @
            fri_decommitment_transcript i (drop (Suc j) ?bl) @ rest\<rparr>"
      using invD drop_eq unfolding fri_decommitment_transcript.simps
      by simp
    have len_pow: "\<exists>K. length (ls ! j) = 2 ^ K"
      using len_pow_suc by blast
    then obtain K where len_pow_K: "length (ls ! j) = 2 ^ K"
      by blast
    have l_eval:
      "ls ! j = map (poly (ps ! j)) (ds ! j)"
      by (rule layers) (use j_lt len_ps len_ds len_ls in simp_all)
    have d_len: "length (ds ! j) = length (ls ! j)"
      using l_eval by simp
    have i_d_bound: "i < length (ds ! j)"
      using i_bound invD d_len by simp
    have d_i:
      "ds ! j ! i = ((p.h ^ i) * shift) ^ pw"
      using fri_commit_outcome_initial_domain_points[OF fri j_le i_d_bound] invD by simp
    have sidx_bound:
      "(i + len div 2) mod len < length (ds ! j)"
      using len_pos invD d_len by simp
    have d_sib:
      "ds ! j ! ((i + len div 2) mod len) =
        ((p.h ^ ((i + len div 2) mod len)) * shift) ^ pw"
      using fri_commit_outcome_initial_domain_points[OF fri j_le sidx_bound] invD
      by simp
    have next_len:
      "length (ls ! Suc j) = length (ls ! j) div 2"
      using next_fri_layer_length[OF successors[OF j_lt]] d_len by simp
    have half_pos: "0 < len div 2"
      using invD len_pow_suc by simp
    have even_len: "2 dvd len"
      using invD len_pow_suc by simp
    have round: "len * pw = clength * scale"
    proof -
      have "len * pw = 2 ^ (N - j) * 2 ^ j"
        using invD len_exact by simp
      also have "... = 2 ^ ((N - j) + j)"
        by (simp add: power_add)
      also have "... = 2 ^ N"
        using j_lt_N by simp
      also have "... = clength * scale"
        using init_domain .
      finally show ?thesis .
    qed
    have next_idx_bound:
      "i mod (len div 2) < length (ds ! Suc j)"
    proof -
      have "length (ds ! Suc j) = length (ls ! Suc j)"
      proof -
        have "ls ! Suc j = map (poly (ps ! Suc j)) (ds ! Suc j)"
          by (rule layers) (use j_lt len_ps len_ds len_ls in simp_all)
        then show ?thesis by simp
      qed
      then show ?thesis
        using next_len half_pos invD by simp
    qed
    have next_domain:
      "ds ! Suc j ! (i mod (len div 2)) =
        ((p.h ^ i) * shift) ^ pw * ((p.h ^ i) * shift) ^ pw"
    proof -
      have suc_le: "Suc j \<le> n"
        using j_lt by simp
      have pw_next: "pw + pw = 2 ^ Suc j"
      proof -
        have "(2::nat) ^ j + 2 ^ j = 2 ^ Suc j"
        proof -
          have "(2::nat) ^ Suc j = 2 * 2 ^ j"
            by (simp add: power_Suc)
          also have "... = 2 ^ j + 2 ^ j"
            by presburger
          finally show ?thesis by simp
        qed
        then show ?thesis
          using invD by simp
      qed
      have point_next:
        "ds ! Suc j ! (i mod (len div 2)) =
          ((p.h ^ (i mod (len div 2))) * shift) ^ (2 ^ Suc j)"
        using fri_commit_outcome_initial_domain_points[OF fri suc_le next_idx_bound]
          invD next_len
        by simp
      have fold_domain:
        "((p.h ^ i) * shift) ^ pw * ((p.h ^ i) * shift) ^ pw =
          ((p.h ^ (i mod (len div 2))) * shift) ^ (pw + pw)"
        by (rule fri_next_domain_round[OF half_pos even_len round])
      show ?thesis
        using point_next fold_domain pw_next by simp
    qed
    have step_eq:
      "m a = fri_verifier_layer (challenges ! j) (roots ! j) i x len pw"
      using receive_query_commits_zip_nth_apply[
          OF j_lt[folded len_challenges] j_lt[folded len_roots],
          of i x len pw]
        m_eq a_eq
      by simp
    have created_j:
      "p.created_tree (ls ! j) (ms ! j) s6"
      by (rule created) (use j_lt len_ls len_ms in simp_all)
    show "None \<notin> dom (dist (execute (m a) st))"
      unfolding step_eq
    proof (rule honest_fri_layer_decommitment_step_created_next_value_domain(1)[
        where rest="fri_decommitment_transcript i (drop (Suc j) ?bl) @ rest"])
      show "p.created_tree (ls ! j) (ms ! j) s6"
        using created_j .
      show "len = length (ls ! j)"
        using invD by simp
      show "length (ls ! j) = 2 ^ K"
        using len_pow_K .
      show "i < len"
        using i_bound .
      show "x = ls ! j ! i"
        using invD by simp
      show "s6 \<le> st"
        using invD by simp
      show "roots ! j = value (ms ! j)"
        by (rule roots_aligned[OF j_lt])
      show "st =
        st\<lparr>PTranscript :=
          fri_layer_decommitment_transcript (ls ! j) (ms ! j) i len @
          fri_decommitment_transcript i (drop (Suc j) ?bl) @ rest\<rparr>"
        using tr_layer .
      show "p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
        by (rule successors[OF j_lt])
      show "ls ! j = map (poly (ps ! j)) (ds ! j)"
        using l_eval .
      show "length (ds ! j) = length (ls ! j)"
        using d_len .
      show "2 dvd len"
        using even_len .
      show "len * pw = clength * scale"
        using round .
      show "ds ! j ! i = (p.h ^ i * shift) ^ pw"
        using d_i .
      show "ds ! j ! ((i + len div 2) mod len) =
        (p.h ^ ((i + len div 2) mod len) * shift) ^ pw"
        using d_sib .
      show "i mod (len div 2) < length (ds ! Suc j)"
        using next_idx_bound .
      show "ds ! Suc j ! (i mod (len div 2)) =
        (p.h ^ i * shift) ^ pw * (p.h ^ i * shift) ^ pw"
        using next_domain .
    qed
  qed
  have nf_map:
    "None \<notin> dom (dist (execute
      (mfold (idx, x0, len0, 1) (map (\<lambda>m. m) ?fl)) start))"
  proof (rule no_failure_mfold_map_indexI[
      where I=I and xs="?fl" and F="\<lambda>m. m", OF init_I])
    show "\<And>j m a st. j < length ?fl \<Longrightarrow>
      m = ?fl ! j \<Longrightarrow> I j a st \<Longrightarrow>
      None \<notin> dom (dist (execute (m a) st))"
      by (rule step_nf)
  next
    fix j m a st y t
    assume j_lt_fl: "j < length ?fl"
      and m_eq: "m = ?fl ! j"
      and inv: "I j a st"
      and out: "Some (y, t) \<in> set_dist (execute (m a) st)"
    have j_lt: "j < n"
      using j_lt_fl fl_len by presburger
    obtain i x len pw where a_eq: "a = (i, x, len, pw)"
      by (cases a) auto
    have invD:
      "i = idx mod length (ls ! j)"
      "x = ls ! j ! i"
      "len = length (ls ! j)"
      "pw = 2 ^ j"
      "PTranscript st = fri_decommitment_transcript i (drop j ?bl) @ rest"
      "s6 \<le> st"
      using inv unfolding I_def a_eq by simp_all
    have j_le: "j \<le> n"
      using j_lt by simp
    have len_exact:
      "length (ls ! j) = 2 ^ (N - j)"
      by (rule fri_commit_outcome_initial_layer_length_power[
          OF fri layers init_len n_le_N j_le])
    have j_lt_N: "j < N"
      using j_lt n_le_N by linarith
    have diff_suc: "N - j = Suc (N - Suc j)"
      using j_lt_N by simp
    have len_pow_suc:
      "length (ls ! j) = 2 ^ Suc (N - Suc j)"
      using len_exact diff_suc by simp
    have len_pos: "0 < length (ls ! j)"
      using len_pow_suc by simp
    have i_bound: "i < len"
      using invD len_pos by simp
    have drop_eq:
      "drop j ?bl = (ls ! j, ms ! j) # drop (Suc j) ?bl"
      by (rule butlast_zip_suc_drop_nth[OF len_ls len_ms j_lt])
    have tr_layer:
      "st =
        st\<lparr>PTranscript :=
          fri_layer_decommitment_transcript (ls ! j) (ms ! j) i len @
            fri_decommitment_transcript i (drop (Suc j) ?bl) @ rest\<rparr>"
      using invD drop_eq unfolding fri_decommitment_transcript.simps
      by simp
    obtain K where len_pow_K: "length (ls ! j) = 2 ^ K"
      using len_pow_suc by blast
    have l_eval:
      "ls ! j = map (poly (ps ! j)) (ds ! j)"
      by (rule layers) (use j_lt len_ps len_ds len_ls in simp_all)
    have d_len: "length (ds ! j) = length (ls ! j)"
      using l_eval by simp
    have i_d_bound: "i < length (ds ! j)"
      using i_bound invD d_len by simp
    have d_i:
      "ds ! j ! i = ((p.h ^ i) * shift) ^ pw"
      using fri_commit_outcome_initial_domain_points[OF fri j_le i_d_bound] invD by simp
    have sidx_bound:
      "(i + len div 2) mod len < length (ds ! j)"
      using len_pos invD d_len by simp
    have d_sib:
      "ds ! j ! ((i + len div 2) mod len) =
        ((p.h ^ ((i + len div 2) mod len)) * shift) ^ pw"
      using fri_commit_outcome_initial_domain_points[OF fri j_le sidx_bound] invD
      by simp
    have next_len:
      "length (ls ! Suc j) = length (ls ! j) div 2"
      using next_fri_layer_length[OF successors[OF j_lt]] d_len by simp
    have half_pos: "0 < len div 2"
      using invD len_pow_suc by simp
    have even_len: "2 dvd len"
      using invD len_pow_suc by simp
    have round: "len * pw = clength * scale"
    proof -
      have "len * pw = 2 ^ (N - j) * 2 ^ j"
        using invD len_exact by simp
      also have "... = 2 ^ ((N - j) + j)"
        by (simp add: power_add)
      also have "... = 2 ^ N"
        using j_lt_N by simp
      also have "... = clength * scale"
        using init_domain .
      finally show ?thesis .
    qed
    have next_idx_bound:
      "i mod (len div 2) < length (ds ! Suc j)"
    proof -
      have "length (ds ! Suc j) = length (ls ! Suc j)"
      proof -
        have "ls ! Suc j = map (poly (ps ! Suc j)) (ds ! Suc j)"
          by (rule layers) (use j_lt len_ps len_ds len_ls in simp_all)
        then show ?thesis by simp
      qed
      then show ?thesis
        using next_len half_pos invD by simp
    qed
    have next_domain:
      "ds ! Suc j ! (i mod (len div 2)) =
        ((p.h ^ i) * shift) ^ pw * ((p.h ^ i) * shift) ^ pw"
    proof -
      have suc_le: "Suc j \<le> n"
        using j_lt by simp
      have pw_next: "pw + pw = 2 ^ Suc j"
      proof -
        have "(2::nat) ^ j + 2 ^ j = 2 ^ Suc j"
        proof -
          have "(2::nat) ^ Suc j = 2 * 2 ^ j"
            by (simp add: power_Suc)
          also have "... = 2 ^ j + 2 ^ j"
            by presburger
          finally show ?thesis by simp
        qed
        then show ?thesis
          using invD by simp
      qed
      have point_next:
        "ds ! Suc j ! (i mod (len div 2)) =
          ((p.h ^ (i mod (len div 2))) * shift) ^ (2 ^ Suc j)"
        using fri_commit_outcome_initial_domain_points[OF fri suc_le next_idx_bound]
          invD next_len
        by simp
      have fold_domain:
        "((p.h ^ i) * shift) ^ pw * ((p.h ^ i) * shift) ^ pw =
          ((p.h ^ (i mod (len div 2))) * shift) ^ (pw + pw)"
        by (rule fri_next_domain_round[OF half_pos even_len round])
      show ?thesis
        using point_next fold_domain pw_next by simp
    qed
    have step_eq:
      "m a = fri_verifier_layer (challenges ! j) (roots ! j) i x len pw"
      using receive_query_commits_zip_nth_apply[
          OF j_lt[folded len_challenges] j_lt[folded len_roots],
          of i x len pw]
        m_eq a_eq
      by simp
    have created_j:
      "p.created_tree (ls ! j) (ms ! j) s6"
      by (rule created) (use j_lt len_ls len_ms in simp_all)
    have out':
      "Some (y, t) \<in>
        set_dist (execute
          (fri_verifier_layer (challenges ! j) (roots ! j) i x len pw) st)"
      using out unfolding step_eq .
    have step_res:
      "y =
        (i mod (len div 2), ls ! Suc j ! (i mod (len div 2)),
          len div 2, pw + pw) \<and>
       PTranscript t = fri_decommitment_transcript i (drop (Suc j) ?bl) @ rest \<and>
       st \<le> t"
    proof (rule honest_fri_layer_decommitment_step_created_next_value_domain(2)[
        where rest="fri_decommitment_transcript i (drop (Suc j) ?bl) @ rest"])
      show "p.created_tree (ls ! j) (ms ! j) s6"
        using created_j .
      show "len = length (ls ! j)"
        using invD by simp
      show "length (ls ! j) = 2 ^ K"
        using len_pow_K .
      show "i < len"
        using i_bound .
      show "x = ls ! j ! i"
        using invD by simp
      show "s6 \<le> st"
        using invD by simp
      show "roots ! j = value (ms ! j)"
        by (rule roots_aligned[OF j_lt])
      show "st =
        st\<lparr>PTranscript :=
          fri_layer_decommitment_transcript (ls ! j) (ms ! j) i len @
          fri_decommitment_transcript i (drop (Suc j) ?bl) @ rest\<rparr>"
        using tr_layer .
      show "p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
        by (rule successors[OF j_lt])
      show "ls ! j = map (poly (ps ! j)) (ds ! j)"
        using l_eval .
      show "length (ds ! j) = length (ls ! j)"
        using d_len .
      show "2 dvd len"
        using even_len .
      show "len * pw = clength * scale"
        using round .
      show "ds ! j ! i = (p.h ^ i * shift) ^ pw"
        using d_i .
      show "ds ! j ! ((i + len div 2) mod len) =
        (p.h ^ ((i + len div 2) mod len) * shift) ^ pw"
        using d_sib .
      show "i mod (len div 2) < length (ds ! Suc j)"
        using next_idx_bound .
      show "ds ! Suc j ! (i mod (len div 2)) =
        (p.h ^ i * shift) ^ pw * (p.h ^ i * shift) ^ pw"
        using next_domain .
      show "Some (y, t) \<in>
        set_dist (execute
          (fri_verifier_layer (challenges ! j) (roots ! j) i x len pw) st)"
        using out' .
    qed
    have i_next:
      "i mod (len div 2) = idx mod length (ls ! Suc j)"
    proof -
      have mod_half:
        "(idx mod length (ls ! j)) mod (length (ls ! j) div 2) =
          idx mod (length (ls ! j) div 2)"
        by (rule mod_mod_half_power[OF len_pow_suc])
      show ?thesis
        using invD next_len mod_half by simp
    qed
    have pw_next: "pw + pw = 2 ^ Suc j"
    proof -
      have "(2::nat) ^ j + 2 ^ j = 2 ^ Suc j"
      proof -
        have "(2::nat) ^ Suc j = 2 * 2 ^ j"
          by (simp add: power_Suc)
        also have "... = 2 ^ j + 2 ^ j"
          by presburger
        finally show ?thesis by simp
      qed
      then show ?thesis
        using invD by simp
    qed
    have tr_next:
      "PTranscript t =
        fri_decommitment_transcript (i mod (len div 2))
          (drop (Suc j) ?bl) @ rest"
    proof -
      have bridge:
        "fri_decommitment_transcript (idx mod length (ls ! j))
            (drop (Suc j) ?bl) =
          fri_decommitment_transcript
            (idx mod (length (ls ! j) div 2))
            (drop (Suc j) ?bl)"
        by (rule fri_decommitment_transcript_drop_half_index[
            OF len_ls len_ms j_lt len_pow_suc next_len])
      have mod_half:
        "(idx mod length (ls ! j)) mod (length (ls ! j) div 2) =
          idx mod (length (ls ! j) div 2)"
        by (rule mod_mod_half_power[OF len_pow_suc])
      have bridge':
        "fri_decommitment_transcript (idx mod (length (ls ! j) div 2))
            (drop (Suc j) ?bl) =
          fri_decommitment_transcript
            (idx mod length (ls ! j) mod (length (ls ! j) div 2))
            (drop (Suc j) ?bl)"
        using mod_half by simp
      show ?thesis
        using step_res bridge bridge' invD by simp
    qed
    have ext_next: "s6 \<le> t"
      using invD step_res by (meson p.hash_ext_trans)
    have len_half: "len div 2 = length (ls ! Suc j)"
      using invD next_len by simp
    show "I (Suc j) y t"
      using step_res i_next pw_next tr_next ext_next next_len invD(3) len_half
      unfolding I_def
      by (simp add: split: prod.splits)
  qed
  show ?thesis
    using nf_map by simp
qed

lemma honest_fri_decommitments_mfold_outcome:
  assumes fri:
    "fri_commit_outcome n cp p.eval_domain l0 m0 ps ds ls ms s5 s6"
    and len_ps: "length ps = Suc n"
    and len_ds: "length ds = Suc n"
    and len_ls: "length ls = Suc n"
    and len_ms: "length ms = Suc n"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and created:
      "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
        p.created_tree (ls ! i) (ms ! i) s6"
    and init_len: "length l0 = 2 ^ N"
    and init_domain: "2 ^ N = clength * scale"
    and n_le_N: "n \<le> N"
    and len_roots: "length roots = n"
    and len_challenges: "length challenges = n"
    and roots_aligned: "\<And>j. j < n \<Longrightarrow> roots ! j = value (ms ! j)"
    and successors:
      "\<And>j. j < n \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and idx_bound: "idx < length (ls ! 0)"
    and x0_eq: "x0 = ls ! 0 ! idx"
    and len0_eq: "len0 = length (ls ! 0)"
    and start_tr:
      "PTranscript start = fri_decommitment_transcript idx (butlast (zip ls ms)) @ rest"
    and start_ext: "s6 \<le> start"
    and outcome:
      "Some ((i, x, len, pw), t) \<in>
        set_dist (execute
          (mfold (idx, x0, len0, 1)
            (v.receive_query_commits (zip challenges roots))) start)"
  shows
    "i = idx mod length (ls ! n) \<and>
     x = ls ! n ! i \<and>
     len = length (ls ! n) \<and>
	     pw = 2 ^ n \<and>
	     PTranscript t =
	       fri_decommitment_transcript i (drop n (butlast (zip ls ms))) @ rest \<and>
	     PState t =
	       foldl concat (PState start)
	         (fri_decommitment_transcript idx (butlast (zip ls ms))) \<and>
	     s6 \<le> t"
proof -
  let ?fl =
    "v.receive_query_commits (zip challenges roots) ::
      ((nat \<times> 'f \<times> nat \<times> nat) \<Rightarrow>
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) list"
  let ?bl = "butlast (zip ls ms)"
  define I where
    "I = (\<lambda>(j::nat) (a::nat \<times> 'f \<times> nat \<times> nat)
        (s::'f protocol_channel).
      (case a of (i, x, len, pw) \<Rightarrow>
        i = idx mod length (ls ! j) \<and>
        x = ls ! j ! i \<and>
	        len = length (ls ! j) \<and>
	        pw = 2 ^ j \<and>
	        PTranscript s = fri_decommitment_transcript i (drop j ?bl) @ rest \<and>
	        (\<exists>consumed.
	          fri_decommitment_transcript idx ?bl =
	            consumed @ fri_decommitment_transcript i (drop j ?bl) \<and>
	          PState s = foldl concat (PState start) consumed) \<and>
	        s6 \<le> s))"
  have fl_len: "length ?fl = n"
    using len_roots len_challenges
    unfolding v.receive_query_commits_def by simp
  have init_I: "I 0 (idx, x0, len0, 1) start"
    unfolding I_def
    using idx_bound x0_eq len0_eq start_tr start_ext by simp
  have outcome_map:
    "Some ((i, x, len, pw), t) \<in>
      set_dist (execute
        (mfold (idx, x0, len0, 1) (map (\<lambda>m. m) ?fl)) start)"
    using outcome by simp
  have final_I: "I (length ?fl) (i, x, len, pw) t"
  proof (rule mfold_map_index_outcome_invariantI[
      where I=I and xs="?fl" and F="\<lambda>m. m", OF init_I _ outcome_map])
    fix j m a st y t'
    assume j_lt_fl: "j < length ?fl"
      and m_eq: "m = ?fl ! j"
      and inv: "I j a st"
      and out: "Some (y, t') \<in> set_dist (execute (m a) st)"
    have j_lt: "j < n"
      using j_lt_fl fl_len by presburger
    obtain ii xx lenn pww where a_eq: "a = (ii, xx, lenn, pww)"
      by (cases a) auto
    have invD:
      "ii = idx mod length (ls ! j)"
      "xx = ls ! j ! ii"
	      "lenn = length (ls ! j)"
	      "pww = 2 ^ j"
	      "PTranscript st = fri_decommitment_transcript ii (drop j ?bl) @ rest"
	      "s6 \<le> st"
	      using inv unfolding I_def a_eq by simp_all
	    have consumed_ex:
	      "\<exists>consumed.
	        fri_decommitment_transcript idx ?bl =
	          consumed @ fri_decommitment_transcript ii (drop j ?bl) \<and>
	        PState st = foldl concat (PState start) consumed"
	      using inv invD(1) unfolding I_def a_eq by simp
	    from consumed_ex obtain consumed where
	      consumed_total:
	        "fri_decommitment_transcript idx ?bl =
	          consumed @ fri_decommitment_transcript ii (drop j ?bl)"
	      and consumed_state:
	        "PState st = foldl concat (PState start) consumed"
	      by blast
    have j_le: "j \<le> n"
      using j_lt by simp
    have len_exact:
      "length (ls ! j) = 2 ^ (N - j)"
      by (rule fri_commit_outcome_initial_layer_length_power[
          OF fri layers init_len n_le_N j_le])
    have j_lt_N: "j < N"
      using j_lt n_le_N by linarith
    have diff_suc: "N - j = Suc (N - Suc j)"
      using j_lt_N by simp
    have len_pow_suc:
      "length (ls ! j) = 2 ^ Suc (N - Suc j)"
      using len_exact diff_suc by simp
    have len_pos: "0 < length (ls ! j)"
      using len_pow_suc by simp
    have ii_bound: "ii < lenn"
      using invD len_pos by simp
    have drop_eq:
      "drop j ?bl = (ls ! j, ms ! j) # drop (Suc j) ?bl"
      by (rule butlast_zip_suc_drop_nth[OF len_ls len_ms j_lt])
    have tr_layer:
      "st =
        st\<lparr>PTranscript :=
          fri_layer_decommitment_transcript (ls ! j) (ms ! j) ii lenn @
            fri_decommitment_transcript ii (drop (Suc j) ?bl) @ rest\<rparr>"
      using invD drop_eq unfolding fri_decommitment_transcript.simps
      by simp
    obtain K where len_pow_K: "length (ls ! j) = 2 ^ K"
      using len_pow_suc by blast
    have l_eval:
      "ls ! j = map (poly (ps ! j)) (ds ! j)"
      by (rule layers) (use j_lt len_ps len_ds len_ls in simp_all)
    have d_len: "length (ds ! j) = length (ls ! j)"
      using l_eval by simp
    have ii_d_bound: "ii < length (ds ! j)"
      using ii_bound invD d_len by simp
    have d_i:
      "ds ! j ! ii = ((p.h ^ ii) * shift) ^ pww"
      using fri_commit_outcome_initial_domain_points[OF fri j_le ii_d_bound] invD by simp
    have sidx_bound:
      "(ii + lenn div 2) mod lenn < length (ds ! j)"
      using len_pos invD d_len by simp
    have d_sib:
      "ds ! j ! ((ii + lenn div 2) mod lenn) =
        ((p.h ^ ((ii + lenn div 2) mod lenn)) * shift) ^ pww"
      using fri_commit_outcome_initial_domain_points[OF fri j_le sidx_bound] invD
      by simp
    have next_len:
      "length (ls ! Suc j) = length (ls ! j) div 2"
      using next_fri_layer_length[OF successors[OF j_lt]] d_len by simp
    have half_pos: "0 < lenn div 2"
      using invD len_pow_suc by simp
    have even_len: "2 dvd lenn"
      using invD len_pow_suc by simp
    have round: "lenn * pww = clength * scale"
    proof -
      have "lenn * pww = 2 ^ (N - j) * 2 ^ j"
        using invD len_exact by simp
      also have "... = 2 ^ ((N - j) + j)"
        by (simp add: power_add)
      also have "... = 2 ^ N"
        using j_lt_N by simp
      also have "... = clength * scale"
        using init_domain .
      finally show ?thesis .
    qed
    have next_idx_bound:
      "ii mod (lenn div 2) < length (ds ! Suc j)"
    proof -
      have "length (ds ! Suc j) = length (ls ! Suc j)"
      proof -
        have "ls ! Suc j = map (poly (ps ! Suc j)) (ds ! Suc j)"
          by (rule layers) (use j_lt len_ps len_ds len_ls in simp_all)
        then show ?thesis by simp
      qed
      then show ?thesis
        using next_len half_pos invD by simp
    qed
    have next_domain:
      "ds ! Suc j ! (ii mod (lenn div 2)) =
        ((p.h ^ ii) * shift) ^ pww * ((p.h ^ ii) * shift) ^ pww"
    proof -
      have suc_le: "Suc j \<le> n"
        using j_lt by simp
      have pw_next: "pww + pww = 2 ^ Suc j"
      proof -
        have "(2::nat) ^ j + 2 ^ j = 2 ^ Suc j"
        proof -
          have "(2::nat) ^ Suc j = 2 * 2 ^ j"
            by (simp add: power_Suc)
          also have "... = 2 ^ j + 2 ^ j"
            by presburger
          finally show ?thesis by simp
        qed
        then show ?thesis
          using invD by simp
      qed
      have point_next:
        "ds ! Suc j ! (ii mod (lenn div 2)) =
          ((p.h ^ (ii mod (lenn div 2))) * shift) ^ (2 ^ Suc j)"
        using fri_commit_outcome_initial_domain_points[OF fri suc_le next_idx_bound]
          invD next_len
        by simp
      have fold_domain:
        "((p.h ^ ii) * shift) ^ pww * ((p.h ^ ii) * shift) ^ pww =
          ((p.h ^ (ii mod (lenn div 2))) * shift) ^ (pww + pww)"
        by (rule fri_next_domain_round[OF half_pos even_len round])
      show ?thesis
        using point_next fold_domain pw_next by simp
    qed
    have step_eq:
      "m a = fri_verifier_layer (challenges ! j) (roots ! j) ii xx lenn pww"
      using receive_query_commits_zip_nth_apply[
          OF j_lt[folded len_challenges] j_lt[folded len_roots],
          of ii xx lenn pww]
        m_eq a_eq
      by simp
    have created_j:
      "p.created_tree (ls ! j) (ms ! j) s6"
      by (rule created) (use j_lt len_ls len_ms in simp_all)
    have out':
      "Some (y, t') \<in>
        set_dist (execute
          (fri_verifier_layer (challenges ! j) (roots ! j) ii xx lenn pww) st)"
      using out unfolding step_eq .
    have step_res:
	      "y =
	        (ii mod (lenn div 2), ls ! Suc j ! (ii mod (lenn div 2)),
	          lenn div 2, pww + pww) \<and>
	       PTranscript t' = fri_decommitment_transcript ii (drop (Suc j) ?bl) @ rest \<and>
	       st \<le> t' \<and>
	       PState t' =
	         foldl concat (PState st)
	           (fri_layer_decommitment_transcript (ls ! j) (ms ! j) ii lenn)"
	    proof (rule honest_fri_layer_decommitment_step_created_next_value_domain_state[
	        where rest="fri_decommitment_transcript ii (drop (Suc j) ?bl) @ rest"])
      show "p.created_tree (ls ! j) (ms ! j) s6"
        using created_j .
      show "lenn = length (ls ! j)"
        using invD by simp
      show "length (ls ! j) = 2 ^ K"
        using len_pow_K .
      show "ii < lenn"
        using ii_bound .
      show "xx = ls ! j ! ii"
        using invD by simp
      show "s6 \<le> st"
        using invD by simp
      show "roots ! j = value (ms ! j)"
        by (rule roots_aligned[OF j_lt])
      show "st =
        st\<lparr>PTranscript :=
          fri_layer_decommitment_transcript (ls ! j) (ms ! j) ii lenn @
          fri_decommitment_transcript ii (drop (Suc j) ?bl) @ rest\<rparr>"
        using tr_layer .
      show "p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
        by (rule successors[OF j_lt])
      show "ls ! j = map (poly (ps ! j)) (ds ! j)"
        using l_eval .
      show "length (ds ! j) = length (ls ! j)"
        using d_len .
      show "2 dvd lenn"
        using even_len .
      show "lenn * pww = clength * scale"
        using round .
      show "ds ! j ! ii = (p.h ^ ii * shift) ^ pww"
        using d_i .
      show "ds ! j ! ((ii + lenn div 2) mod lenn) =
        (p.h ^ ((ii + lenn div 2) mod lenn) * shift) ^ pww"
        using d_sib .
      show "ii mod (lenn div 2) < length (ds ! Suc j)"
        using next_idx_bound .
      show "ds ! Suc j ! (ii mod (lenn div 2)) =
        (p.h ^ ii * shift) ^ pww * (p.h ^ ii * shift) ^ pww"
        using next_domain .
      show "Some (y, t') \<in>
        set_dist (execute
          (fri_verifier_layer (challenges ! j) (roots ! j) ii xx lenn pww) st)"
        using out' .
    qed
    have i_next:
      "ii mod (lenn div 2) = idx mod length (ls ! Suc j)"
    proof -
      have mod_half:
        "(idx mod length (ls ! j)) mod (length (ls ! j) div 2) =
          idx mod (length (ls ! j) div 2)"
        by (rule mod_mod_half_power[OF len_pow_suc])
      show ?thesis
        using invD next_len mod_half by simp
    qed
    have pw_next: "pww + pww = 2 ^ Suc j"
    proof -
      have "(2::nat) ^ j + 2 ^ j = 2 ^ Suc j"
      proof -
        have "(2::nat) ^ Suc j = 2 * 2 ^ j"
          by (simp add: power_Suc)
        also have "... = 2 ^ j + 2 ^ j"
          by presburger
        finally show ?thesis by simp
      qed
      then show ?thesis
        using invD by simp
    qed
	    have tail_bridge:
	      "fri_decommitment_transcript ii (drop (Suc j) ?bl) =
	        fri_decommitment_transcript (ii mod (lenn div 2))
	          (drop (Suc j) ?bl)"
	    proof -
	      have bridge:
	        "fri_decommitment_transcript (idx mod length (ls ! j))
            (drop (Suc j) ?bl) =
          fri_decommitment_transcript
            (idx mod (length (ls ! j) div 2))
            (drop (Suc j) ?bl)"
        by (rule fri_decommitment_transcript_drop_half_index[
            OF len_ls len_ms j_lt len_pow_suc next_len])
      have mod_half:
        "(idx mod length (ls ! j)) mod (length (ls ! j) div 2) =
          idx mod (length (ls ! j) div 2)"
        by (rule mod_mod_half_power[OF len_pow_suc])
      have bridge':
	        "fri_decommitment_transcript (idx mod (length (ls ! j) div 2))
	            (drop (Suc j) ?bl) =
	          fri_decommitment_transcript
	            (idx mod length (ls ! j) mod (length (ls ! j) div 2))
	            (drop (Suc j) ?bl)"
	        using mod_half by simp
	      show ?thesis
	        using bridge bridge' invD by simp
	    qed
	    have tr_next:
	      "PTranscript t' =
	        fri_decommitment_transcript (ii mod (lenn div 2))
	          (drop (Suc j) ?bl) @ rest"
	      using step_res tail_bridge by simp
    have ext_next: "s6 \<le> t'"
      using invD step_res by (meson p.hash_ext_trans)
	    have len_half: "lenn div 2 = length (ls ! Suc j)"
	      using invD next_len by simp
	    have consumed_next:
	      "fri_decommitment_transcript idx ?bl =
	        (consumed @
	          fri_layer_decommitment_transcript (ls ! j) (ms ! j) ii lenn) @
	        fri_decommitment_transcript (ii mod (lenn div 2))
	          (drop (Suc j) ?bl)"
	    proof -
	      have tail_split:
	        "fri_decommitment_transcript ii (drop j ?bl) =
	          fri_layer_decommitment_transcript (ls ! j) (ms ! j) ii lenn @
	          fri_decommitment_transcript ii (drop (Suc j) ?bl)"
	        using drop_eq invD unfolding fri_decommitment_transcript.simps by simp
	      show ?thesis
	        using consumed_total tail_split tail_bridge by simp
	    qed
	    have state_next:
	      "PState t' =
	        foldl concat (PState start)
	          (consumed @
	            fri_layer_decommitment_transcript (ls ! j) (ms ! j) ii lenn)"
	      using step_res consumed_state by simp
	    show "I (Suc j) y t'"
	      using step_res i_next pw_next tr_next ext_next next_len invD(3) len_half
	        consumed_next state_next
	      unfolding I_def
	      by (simp add: split: prod.splits)
	  qed
	  show ?thesis
	  proof -
	    have bl_len: "length ?bl = n"
	      using butlast_zip_suc_lengths[OF len_ls len_ms] len_ls len_ms by simp
	    obtain consumed where
	      consumed_total:
	        "fri_decommitment_transcript idx ?bl =
	          consumed @ fri_decommitment_transcript i (drop (length ?fl) ?bl)"
	      and consumed_state:
	        "PState t = foldl concat (PState start) consumed"
	      using final_I unfolding I_def by auto
	    have drop_empty: "drop (length ?fl) ?bl = []"
	      using fl_len bl_len by simp
	    have consumed_eq: "consumed = fri_decommitment_transcript idx ?bl"
	      using consumed_total drop_empty by simp
	    show ?thesis
	      using final_I fl_len consumed_state consumed_eq unfolding I_def by simp
	  qed
	qed

lemma honest_query_prefix_fri_mfold_no_failure:
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
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and len_ms: "length ms = Suc nrounds"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and created:
      "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
        p.created_tree (ls ! i) (ms ! i) s6"
    and init_len: "length (p.cp_eval as) = 2 ^ N"
    and n_le_N: "nrounds \<le> N"
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
    and prefix_out:
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
    and fl_eq: "fl = zip challenges roots"
    and len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and roots_aligned: "\<And>j. j < nrounds \<Longrightarrow> roots ! j = value (ms ! j)"
    and successors:
      "\<And>j. j < nrounds \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
  shows
    "None \<notin> dom (dist (execute
      (mfold
        (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
        (v.receive_query_commits fl)) t))"
proof -
	  have ls0: "ls ! 0 = p.cp_eval as"
	    using fri_commit_initial_heads(3)[OF fri] .
  have idx_bound: "idx' < length (ls ! 0)"
    using idx_def index_less_domain cp_eval_length ls0 by simp
  have x0_eq:
    "v.cp_eval as' fv (p.h ^ idx' * shift) = ls ! 0 ! idx'"
  proof -
    have value_eq:
      "v.cp_eval as' fv (p.h ^ idx' * shift) =
        poly (p.cp as p.f_powers) (p.h ^ idx' * shift)"
      by (rule honest_query_prefix_initial_fri_value[
          OF htv create_f send_f alphas cp'_def send_degree create_cp fri
            final_send random_idx idx_def query_decommit fri_decommit
            prover_state_eq replay prefix_out])
    have ls0_value:
      "ls ! 0 ! idx' =
      poly (p.cp as p.f_powers) (p.h ^ idx' * shift)"
      using cp_eval_index_value[of as "to_nat idx"] idx_def ls0 by simp
    show ?thesis
      using value_eq ls0_value by simp
  qed
  have len0_eq: "clength * scale = length (ls ! 0)"
    using ls0 cp_eval_length by simp
	  have init_domain: "2 ^ N = clength * scale"
	    using init_len cp_eval_length by simp
  have fri_shape:
    "fri_commit_outcome nrounds cp' p.eval_domain (p.cp_eval as) cp_merkle
      ps ds ls ms s5 s6"
    by (rule fri_commit_outcomeI[OF fri])
  have tr_t:
    "PTranscript t = fri_decommitment_transcript idx' (butlast (zip ls ms))"
    by (rule honest_query_prefix_leaves_fri_decommitment_transcript[
        OF htv create_f send_f alphas cp'_def send_degree create_cp fri
          final_send random_idx idx_def query_decommit fri_decommit
          prover_state_eq replay prefix_out])
  have replay_t: "replay_state \<le> t"
    using honest_root_alpha_degree_fri_final_query_from_prover_outcome[
      OF htv create_f send_f alphas cp'_def send_degree create_cp fri
        final_send random_idx idx_def query_decommit fri_decommit
        prover_state_eq replay prefix_out]
    by blast
  have s6_prover: "s6 \<le> prover_state"
    by (rule prover_after_fri_hash_extends[
        OF final_send random_idx query_decommit fri_decommit prover_state_eq])
  have s6_replay: "s6 \<le> replay_state"
    using s6_prover replay
    unfolding verifier_replay_state_def less_eq_hash_ext_def less_eq_fmap_def
    by simp
  have s6_t: "s6 \<le> t"
    using s6_replay replay_t by (meson p.hash_ext_trans)
  have tr_t_empty:
    "PTranscript t = fri_decommitment_transcript idx' (butlast (zip ls ms)) @ []"
    using tr_t by simp
  show ?thesis
    unfolding fl_eq
    by (rule honest_fri_decommitments_mfold_no_failure[
        OF fri_shape len_ps len_ds len_ls len_ms layers created init_len init_domain n_le_N
          len_roots len_challenges roots_aligned successors idx_bound x0_eq
          len0_eq tr_t_empty s6_t])
qed

lemma honest_query_prefix_fri_mfold_outcome:
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
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and len_ms: "length ms = Suc nrounds"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and created:
      "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
        p.created_tree (ls ! i) (ms ! i) s6"
    and init_len: "length (p.cp_eval as) = 2 ^ N"
    and n_le_N: "nrounds \<le> N"
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
    and prefix_out:
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
    and fl_eq: "fl = zip challenges roots"
    and len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and roots_aligned: "\<And>j. j < nrounds \<Longrightarrow> roots ! j = value (ms ! j)"
    and successors:
      "\<And>j. j < nrounds \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and outcome:
      "Some ((i, x, len, pw), u) \<in>
        set_dist (execute
          (mfold
            (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
            (v.receive_query_commits fl)) t)"
  shows
    "i = idx' mod length (ls ! nrounds) \<and>
     x = ls ! nrounds ! i \<and>
     len = length (ls ! nrounds) \<and>
     pw = 2 ^ nrounds \<and>
     PTranscript u =
       fri_decommitment_transcript i (drop nrounds (butlast (zip ls ms))) \<and>
     s6 \<le> u"
proof -
  have ls0: "ls ! 0 = p.cp_eval as"
    using fri_commit_initial_heads(3)[OF fri] .
  have idx_bound: "idx' < length (ls ! 0)"
    using idx_def index_less_domain cp_eval_length ls0 by simp
  have x0_eq:
    "v.cp_eval as' fv (p.h ^ idx' * shift) = ls ! 0 ! idx'"
  proof -
    have value_eq:
      "v.cp_eval as' fv (p.h ^ idx' * shift) =
        poly (p.cp as p.f_powers) (p.h ^ idx' * shift)"
      by (rule honest_query_prefix_initial_fri_value[
          OF htv create_f send_f alphas cp'_def send_degree create_cp fri
            final_send random_idx idx_def query_decommit fri_decommit
            prover_state_eq replay prefix_out])
    have ls0_value:
      "ls ! 0 ! idx' =
      poly (p.cp as p.f_powers) (p.h ^ idx' * shift)"
      using cp_eval_index_value[of as "to_nat idx"] idx_def ls0 by simp
    show ?thesis
      using value_eq ls0_value by simp
  qed
  have len0_eq: "clength * scale = length (ls ! 0)"
    using ls0 cp_eval_length by simp
  have init_domain: "2 ^ N = clength * scale"
    using init_len cp_eval_length by simp
  have fri_shape:
    "fri_commit_outcome nrounds cp' p.eval_domain (p.cp_eval as) cp_merkle
      ps ds ls ms s5 s6"
    by (rule fri_commit_outcomeI[OF fri])
  have tr_t:
    "PTranscript t = fri_decommitment_transcript idx' (butlast (zip ls ms))"
    by (rule honest_query_prefix_leaves_fri_decommitment_transcript[
        OF htv create_f send_f alphas cp'_def send_degree create_cp fri
          final_send random_idx idx_def query_decommit fri_decommit
          prover_state_eq replay prefix_out])
  have replay_t: "replay_state \<le> t"
    using honest_root_alpha_degree_fri_final_query_from_prover_outcome[
      OF htv create_f send_f alphas cp'_def send_degree create_cp fri
        final_send random_idx idx_def query_decommit fri_decommit
        prover_state_eq replay prefix_out]
    by blast
  have s6_prover: "s6 \<le> prover_state"
    by (rule prover_after_fri_hash_extends[
        OF final_send random_idx query_decommit fri_decommit prover_state_eq])
  have s6_replay: "s6 \<le> replay_state"
    using s6_prover replay
    unfolding verifier_replay_state_def less_eq_hash_ext_def less_eq_fmap_def
    by simp
  have s6_t: "s6 \<le> t"
    using s6_replay replay_t by (meson p.hash_ext_trans)
  have outcome_zip:
    "Some ((i, x, len, pw), u) \<in>
      set_dist (execute
        (mfold
          (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
          (v.receive_query_commits (zip challenges roots))) t)"
    using outcome fl_eq by simp
  have tr_t_empty:
    "PTranscript t = fri_decommitment_transcript idx' (butlast (zip ls ms)) @ []"
    using tr_t by simp
  have res:
    "i = idx' mod length (ls ! nrounds) \<and>
     x = ls ! nrounds ! i \<and>
     len = length (ls ! nrounds) \<and>
	     pw = 2 ^ nrounds \<and>
	     PTranscript u =
	       fri_decommitment_transcript i (drop nrounds (butlast (zip ls ms))) @ [] \<and>
	     PState u =
	       foldl concat (PState t)
	         (fri_decommitment_transcript idx' (butlast (zip ls ms))) \<and>
	     s6 \<le> u"
    by (rule honest_fri_decommitments_mfold_outcome[
        OF fri_shape len_ps len_ds len_ls len_ms layers created init_len init_domain n_le_N
          len_roots len_challenges roots_aligned successors idx_bound x0_eq
          len0_eq tr_t_empty s6_t outcome_zip])
  show ?thesis
    using res by simp
qed

lemma honest_query_prefix_final_assert_no_failure:
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
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and len_ms: "length ms = Suc nrounds"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and created:
      "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
        p.created_tree (ls ! i) (ms ! i) s6"
    and init_len: "length (p.cp_eval as) = 2 ^ N"
    and n_le_N: "nrounds \<le> N"
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
    and prefix_out:
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
    and fl_eq: "fl = zip challenges roots"
    and len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and roots_aligned: "\<And>j. j < nrounds \<Longrightarrow> roots ! j = value (ms ! j)"
    and successors:
      "\<And>j. j < nrounds \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and fold_out:
      "Some ((i, x, len, pw), u) \<in>
        set_dist (execute
          (mfold
            (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
            (v.receive_query_commits fl)) t)"
  shows "None \<notin> dom (dist (execute (assert (x = final)) u))"
proof -
  have fold_res:
    "i = idx' mod length (ls ! nrounds) \<and>
     x = ls ! nrounds ! i \<and>
     len = length (ls ! nrounds) \<and>
     pw = 2 ^ nrounds \<and>
     PTranscript u =
       fri_decommitment_transcript i (drop nrounds (butlast (zip ls ms))) \<and>
     s6 \<le> u"
    by (rule honest_query_prefix_fri_mfold_outcome[
        OF htv create_f send_f alphas cp'_def send_degree create_cp fri
          len_ps len_ds len_ls len_ms layers created init_len n_le_N
          final_send random_idx idx_def query_decommit fri_decommit prover_state_eq
          replay prefix_out fl_eq len_roots len_challenges roots_aligned successors
          fold_out])
  have prefix_res:
    "final = hd (last ls)"
    using honest_root_alpha_degree_fri_final_query_from_prover_outcome[
      OF htv create_f send_f alphas cp'_def send_degree create_cp fri
        final_send random_idx idx_def query_decommit fri_decommit prover_state_eq
        replay prefix_out]
    by blast
  have i_bound: "i < length (ls ! nrounds)"
  proof -
    have len_pos: "0 < length (ls ! nrounds)"
      using fri_commit_initial_layer_length_power[OF fri layers init_len n_le_N, of nrounds]
      by simp
    then show ?thesis
      using fold_res by simp
  qed
  have final_layer:
    "ls ! nrounds ! i = hd (last ls)"
    by (rule honest_fri_final_layer_equals_sent[
        OF fri len_ps len_ds len_ls layers init_len n_le_N nrounds_def
          successors i_bound])
  have "x = final"
    using fold_res prefix_res final_layer by simp
  then show ?thesis
    by (simp add: assert_def)
qed

lemma honest_query_prefix_fri_mfold_final_no_failure:
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
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and len_ms: "length ms = Suc nrounds"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and created:
      "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
        p.created_tree (ls ! i) (ms ! i) s6"
    and init_len: "length (p.cp_eval as) = 2 ^ N"
    and n_le_N: "nrounds \<le> N"
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
    and prefix_out:
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
    and fl_eq: "fl = zip challenges roots"
    and len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and roots_aligned: "\<And>j. j < nrounds \<Longrightarrow> roots ! j = value (ms ! j)"
    and successors:
      "\<And>j. j < nrounds \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
  shows
    "None \<notin> dom (dist (execute
      (do {
        (i, x, len, pw) \<leftarrow>
          mfold
            (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
            (v.receive_query_commits fl);
        assert (x = final)
      }) t))"
proof (rule no_failure_bindI)
  show "None \<notin> dom (dist (execute
    (mfold
      (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
      (v.receive_query_commits fl)) t))"
    by (rule honest_query_prefix_fri_mfold_no_failure[
        OF htv create_f send_f alphas cp'_def send_degree create_cp fri
          len_ps len_ds len_ls len_ms layers created init_len n_le_N
          final_send random_idx idx_def query_decommit fri_decommit prover_state_eq
          replay prefix_out fl_eq len_roots len_challenges roots_aligned successors])
next
  fix fold_result u
  assume fold_out:
    "Some (fold_result, u) \<in>
      set_dist (execute
        (mfold
          (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
          (v.receive_query_commits fl)) t)"
  obtain i x len pw where fold_result_eq: "fold_result = (i, x, len, pw)"
    by (cases fold_result)
  have fold_out':
    "Some ((i, x, len, pw), u) \<in>
      set_dist (execute
        (mfold
          (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
          (v.receive_query_commits fl)) t)"
    using fold_out unfolding fold_result_eq .
  have assert_nf: "None \<notin> dom (dist (execute (assert (x = final)) u))"
    by (rule honest_query_prefix_final_assert_no_failure[
        OF htv create_f send_f alphas cp'_def send_degree create_cp nrounds_def
          fri len_ps len_ds len_ls len_ms layers created init_len n_le_N
          final_send random_idx idx_def query_decommit fri_decommit prover_state_eq
          replay prefix_out fl_eq len_roots len_challenges roots_aligned successors
          fold_out'])
  show "None \<notin> dom (dist (execute
    ((case fold_result of (i, x, len, pw) \<Rightarrow> assert (x = final))) u))"
    using assert_nf unfolding fold_result_eq case_prod_unfold by simp
qed

lemma honest_query_prefix_fri_mfold_final_dynamic_no_failure:
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
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and len_ms: "length ms = Suc nrounds"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and created:
      "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
        p.created_tree (ls ! i) (ms ! i) s6"
    and init_len: "length (p.cp_eval as) = 2 ^ N"
    and n_le_N: "nrounds \<le> N"
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
    and prefix_out:
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
    and fl_eq: "fl = zip challenges roots"
    and len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and roots_aligned: "\<And>j. j < nrounds \<Longrightarrow> roots ! j = value (ms ! j)"
    and successors:
      "\<And>j. j < nrounds \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
  shows
    "None \<notin> dom (dist (execute
      (do {
        (i, x, len, pw) \<leftarrow>
          mfold
            (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
            (v.receive_query_commits fl);
        assert (x = final)
      }) t))"
proof -
  have prefix_fixed:
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
    by (rule honest_root_alpha_degree_fri_final_query_dynamic_outcome_to_fixed[
        OF htv create_f send_f alphas cp'_def send_degree create_cp nrounds_def
          fri final_send random_idx idx_def query_decommit fri_decommit prover_state_eq
          replay prefix_out])
  show ?thesis
    by (rule honest_query_prefix_fri_mfold_final_no_failure[
        OF htv create_f send_f alphas cp'_def send_degree create_cp nrounds_def
          fri len_ps len_ds len_ls len_ms layers created init_len n_le_N
          final_send random_idx idx_def query_decommit fri_decommit prover_state_eq
          replay prefix_fixed fl_eq len_roots len_challenges roots_aligned successors])
qed

lemma honest_verifier_query_round_no_failure_from_state:
  assumes htv: "honest_trace_valid"
    and create_f:
      "Some (f_merkle, s1) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and trace_fri:
      "Some ((f_ps, f_ds, f_ls, f_ms), s_trace_fri) \<in>
        set_dist (execute
          (p.trace_fri_commit f_nrounds [p.f] [p.eval_domain] [p.f_eval]
            [f_merkle]) s2)"
    and f_len_ps: "length f_ps = Suc f_nrounds"
    and f_len_ds: "length f_ds = Suc f_nrounds"
    and f_len_ls: "length f_ls = Suc f_nrounds"
    and f_len_ms: "length f_ms = Suc f_nrounds"
    and f_layers:
      "\<And>i. i < length f_ps \<Longrightarrow> i < length f_ds \<Longrightarrow> i < length f_ls \<Longrightarrow>
        f_ls ! i = map (poly (f_ps ! i)) (f_ds ! i)"
    and f_created:
      "\<And>i. i < length f_ls \<Longrightarrow> i < length f_ms \<Longrightarrow>
        p.created_tree (f_ls ! i) (f_ms ! i) s_trace_fri"
    and f_init_len: "length p.f_eval = 2 ^ FN"
    and f_n_le_N: "f_nrounds \<le> FN"
    and f_nrounds_def: "f_nrounds = ceil_log clength"
    and f_fl_eq: "f_fl = zip f_challenges f_roots"
    and f_final_eq: "f_final = hd (last f_ls)"
    and f_len_roots: "length f_roots = f_nrounds"
    and f_len_challenges: "length f_challenges = f_nrounds"
    and f_roots_aligned: "\<And>j. j < f_nrounds \<Longrightarrow> f_roots ! j = value (f_ms ! j)"
    and f_successors:
      "\<And>j. j < f_nrounds \<Longrightarrow>
        p.next_fri_layer (f_ps ! j) (f_ds ! j) (f_challenges ! j) =
          (f_ps ! Suc j, f_ds ! Suc j, f_ls ! Suc j)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.composition_fri_commit nrounds [cp'] [p.eval_domain]
            [p.cp_eval as] [cp_merkle]) s5)"
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and len_ms: "length ms = Suc nrounds"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and created:
      "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
        p.created_tree (ls ! i) (ms ! i) s6"
    and init_len: "length (p.cp_eval as) = 2 ^ N"
    and n_le_N: "nrounds \<le> N"
    and nrounds_def: "nrounds = ceil_log (degree cp' + 1)"
    and fr_eq: "fr = value f_merkle"
    and as_eq: "as' = as"
    and fl_eq: "fl = zip challenges roots"
    and final_eq: "final = hd (last ls)"
    and len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and roots_aligned: "\<And>j. j < nrounds \<Longrightarrow> roots ! j = value (ms ! j)"
    and successors:
      "\<And>j. j < nrounds \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and lookup: "fmlookup (HashMap s) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some idx"
    and idx_def: "idx' = p.index (to_nat idx)"
    and query_ext: "s1 \<le> s"
    and trace_fri_ext: "s_trace_fri \<le> s"
    and fri_ext: "s6 \<le> s"
    and transcript:
      "PTranscript s =
        query_decommitment_transcript idx' f_merkle @
        fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
        fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest"
  shows
    "None \<notin> dom (dist (execute (verifier_query_round fr f_fl f_final as' fl final) s))"
proof -
  have ls0: "ls ! 0 = p.cp_eval as"
    using composition_fri_commit_initial_heads(3)[OF fri] .
  have idx_bound: "idx' < length (ls ! 0)"
    using idx_def index_less_domain cp_eval_length ls0 by simp
  have len0_eq: "clength * scale = length (ls ! 0)"
    using ls0 cp_eval_length by simp
  have init_domain: "2 ^ N = clength * scale"
    using init_len cp_eval_length by simp
  have trace_fri_shape:
    "fri_commit_outcome f_nrounds p.f p.eval_domain p.f_eval f_merkle
      f_ps f_ds f_ls f_ms s2 s_trace_fri"
    by (rule trace_fri_commit_outcomeI[OF trace_fri])
  have fri_shape:
    "fri_commit_outcome nrounds cp' p.eval_domain (p.cp_eval as) cp_merkle
      ps ds ls ms s5 s6"
    by (rule composition_fri_commit_outcomeI[OF fri])
  have full_eq:
    "verifier_query_round fr f_fl f_final as' fl final =
      (p.receive_query_index_challenge \<bind> (\<lambda>idxv.
        let idxv' = p.index (to_nat idxv) in
        mmap (v.check_decommit_on_query fr idxv') \<bind> (\<lambda>fv.
        mfold
          (idxv', hd fv, clength * scale, 1)
          (v.receive_query_commits f_fl) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pw).
        assert (f_x = f_final) \<bind> (\<lambda>_.
        mfold
          (idxv', v.cp_eval as' fv (p.h ^ idxv' * shift), clength * scale, 1)
          (v.receive_query_commits fl) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    unfolding verifier_query_round_def by (simp add: Let_def sm_bind_assoc split: prod.splits)
  show ?thesis
    unfolding full_eq
  proof (rule no_failure_bindI)
    show "None \<notin> dom (dist (execute p.receive_query_index_challenge s))"
      by (rule p.receive_query_index_challenge_no_failure)
  next
    fix idxv s_idx
    assume rand:
      "Some (idxv, s_idx) \<in> set_dist (execute p.receive_query_index_challenge s)"
    have rand_res:
      "idxv = idx \<and>
       PState s_idx = PState s \<and>
       PTranscript s_idx = PTranscript s \<and>
       s \<le> s_idx"
      using p.receive_query_index_challenge_known_outcome[OF lookup rand] by simp
    have idxv_def: "p.index (to_nat idxv) = idx'"
      using rand_res idx_def by simp
    have s1_idx: "s1 \<le> s_idx"
      using query_ext rand_res by (meson p.hash_ext_trans)
	    have tr_query:
	      "PTranscript s_idx =
	        query_decommitment_transcript (p.index (to_nat idxv)) f_merkle @
	        fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
	        fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest"
	      using transcript rand_res idxv_def by simp
    have query_nf:
      "None \<notin> dom (dist (execute
        (mmap (v.check_decommit_on_query fr (p.index (to_nat idxv)))) s_idx))"
      by (rule honest_query_decommitment_replay_no_failure[
          OF create_f s1_idx fr_eq tr_query])
    show "None \<notin> dom (dist (execute
      ((let idxv' = p.index (to_nat idxv)
        in mmap (v.check_decommit_on_query fr idxv') \<bind>
          (\<lambda>fv.
            mfold
              (idxv', hd fv, clength * scale, 1)
              (v.receive_query_commits f_fl) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pw).
            assert (f_x = f_final) \<bind> (\<lambda>_.
            mfold
              (idxv', v.cp_eval as' fv (p.h ^ idxv' * shift), clength * scale, 1)
              (v.receive_query_commits fl) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))))) s_idx))"
      unfolding Let_def
    proof (rule no_failure_bindI[OF query_nf])
      fix fv t
      assume query_out:
        "Some (fv, t) \<in>
          set_dist (execute
            (mmap (v.check_decommit_on_query fr (p.index (to_nat idxv)))) s_idx)"
      have paths:
        "\<And>i. i \<in> set (p.powers_scaled (p.index (to_nat idxv))) \<Longrightarrow>
          length (get_authentication_path (length p.f_eval) i f_merkle) =
            floor_log (length p.f_eval)"
        using query_authentication_path_length[OF create_f] by blast
      have query_out_replay:
        "Some (fv, t) \<in>
          set_dist (execute
	            (mmap (v.check_decommit_on_query fr (p.index (to_nat idxv))))
	            (s_idx\<lparr>PTranscript :=
	              query_decommitment_transcript (p.index (to_nat idxv)) f_merkle @
	              fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
	              fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest\<rparr>))"
      proof -
        have upd:
	          "s_idx\<lparr>PTranscript :=
	            query_decommitment_transcript (p.index (to_nat idxv)) f_merkle @
	            fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
	            fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest\<rparr> =
           s_idx"
          using tr_query by simp
        show ?thesis
          using query_out unfolding upd .
      qed
	      have query_res:
	        "fv = map (\<lambda>i. p.f_eval ! i) (p.powers_scaled (p.index (to_nat idxv))) \<and>
		         PTranscript t =
		           fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
		           fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest \<and>
	         PState t =
	           foldl concat (PState s_idx)
	             (query_decommitment_transcript (p.index (to_nat idxv)) f_merkle) \<and>
		         s_idx\<lparr>PTranscript :=
		           query_decommitment_transcript (p.index (to_nat idxv)) f_merkle @
		           fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
		           fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest\<rparr> \<le> t"
        by (rule honest_query_decommitment_replay_outcome[
            OF paths query_out_replay])
      have s_idx_t: "s_idx \<le> t"
      proof -
        have upd:
	          "s_idx\<lparr>PTranscript :=
	            query_decommitment_transcript (p.index (to_nat idxv)) f_merkle @
	            fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
	            fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest\<rparr> =
           s_idx"
          using tr_query by simp
        show ?thesis
          using query_res unfolding upd by simp
      qed
	      have f_ls0: "f_ls ! 0 = p.f_eval"
	        using trace_fri_commit_initial_heads(3)[OF trace_fri] .
	      have f_idx_bound: "idx' < length (f_ls ! 0)"
	        using idx_def index_less_domain f_eval_length f_ls0 by simp
	      have f_len0_eq: "clength * scale = length (f_ls ! 0)"
	        using f_ls0 f_eval_length by simp
	      have f_init_domain: "2 ^ FN = clength * scale"
	        using f_init_len f_eval_length by simp
	      have s_trace_fri_t: "s_trace_fri \<le> t"
	        using trace_fri_ext rand_res s_idx_t by (meson p.hash_ext_trans)
	      have s6_t: "s6 \<le> t"
	        using fri_ext rand_res s_idx_t by (meson p.hash_ext_trans)
	      have f_tr_t:
	        "PTranscript t =
	          fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
	          fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest"
	        using query_res by simp
	      have f_x0_eq: "hd fv = f_ls ! 0 ! idx'"
	      proof -
	        have raw:
	          "hd fv = p.f_eval ! p.index (to_nat idxv)"
	          by (rule honest_initial_trace_fri_accumulator_value)
	            (use query_res in simp_all)
	        show ?thesis
	          using raw idxv_def f_ls0 by simp
	      qed
	      have f_fold_nf:
	        "None \<notin> dom (dist (execute
	          (mfold (idx', hd fv, clength * scale, 1)
	            (v.receive_query_commits f_fl)) t))"
	        unfolding f_fl_eq
	        by (rule honest_fri_decommitments_mfold_no_failure[
	            OF trace_fri_shape f_len_ps f_len_ds f_len_ls f_len_ms f_layers f_created
	              f_init_len f_init_domain f_n_le_N f_len_roots f_len_challenges
	              f_roots_aligned f_successors f_idx_bound f_x0_eq f_len0_eq
	              f_tr_t s_trace_fri_t])
	      show "None \<notin> dom (dist (execute
	        (mfold
	          (p.index (to_nat idxv), hd fv, clength * scale, 1)
	          (v.receive_query_commits f_fl) \<bind>
	        (\<lambda>(f_i, f_x, f_len, f_pw).
	          assert (f_x = f_final) \<bind>
	          (\<lambda>_. mfold
	            (p.index (to_nat idxv),
	              v.cp_eval as' fv (p.h ^ p.index (to_nat idxv) * shift), clength * scale, 1)
	            (v.receive_query_commits fl) \<bind>
	           (\<lambda>(i, x, len, pw). assert (x = final))))) t))"
	        unfolding idxv_def
	      proof (rule no_failure_bindI[OF f_fold_nf])
	        fix f_fold_result t_trace
	        assume f_fold_out:
	          "Some (f_fold_result, t_trace) \<in>
	            set_dist (execute
	              (mfold (idx', hd fv, clength * scale, 1)
	                (v.receive_query_commits f_fl)) t)"
	        obtain f_i f_x f_len f_pw where f_fold_eq:
	          "f_fold_result = (f_i, f_x, f_len, f_pw)"
	          by (cases f_fold_result)
	        have f_fold_out':
	          "Some ((f_i, f_x, f_len, f_pw), t_trace) \<in>
	            set_dist (execute
	              (mfold (idx', hd fv, clength * scale, 1)
	                (v.receive_query_commits f_fl)) t)"
	          using f_fold_out unfolding f_fold_eq .
	        have f_fold_out_zip:
	          "Some ((f_i, f_x, f_len, f_pw), t_trace) \<in>
	            set_dist (execute
	              (mfold (idx', hd fv, clength * scale, 1)
	                (v.receive_query_commits (zip f_challenges f_roots))) t)"
	          using f_fold_out' f_fl_eq by simp
	        have f_fold_res:
	          "f_i = idx' mod length (f_ls ! f_nrounds) \<and>
	           f_x = f_ls ! f_nrounds ! f_i \<and>
	           f_len = length (f_ls ! f_nrounds) \<and>
	           f_pw = 2 ^ f_nrounds \<and>
	           PTranscript t_trace =
	             fri_decommitment_transcript f_i (drop f_nrounds (butlast (zip f_ls f_ms))) @
	             fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest \<and>
	           PState t_trace =
	             foldl concat (PState t)
	               (fri_decommitment_transcript idx' (butlast (zip f_ls f_ms))) \<and>
	           s_trace_fri \<le> t_trace"
	          by (rule honest_fri_decommitments_mfold_outcome[
	              OF trace_fri_shape f_len_ps f_len_ds f_len_ls f_len_ms f_layers f_created
	                f_init_len f_init_domain f_n_le_N f_len_roots f_len_challenges
	                f_roots_aligned f_successors f_idx_bound f_x0_eq f_len0_eq
	                f_tr_t s_trace_fri_t f_fold_out_zip])
		        have f_i_bound: "f_i < length (f_ls ! f_nrounds)"
		        proof -
		          have len_pos: "0 < length (f_ls ! f_nrounds)"
		            using fri_commit_outcome_initial_layer_length_power[
		              OF trace_fri_shape f_layers f_init_len f_n_le_N, of f_nrounds]
		            by simp
		          then show ?thesis
		            using f_fold_res by simp
		        qed
		        have f_rounds_enough:
		          "ceil_log (degree p.f + 1) \<le> f_nrounds"
		          using trace_fri_rounds_enough f_nrounds_def by simp
		        have f_final_layer:
		          "f_ls ! f_nrounds ! f_i = hd (last f_ls)"
		          by (rule honest_fri_final_layer_equals_sent_initial_shape[
		              OF trace_fri_shape f_len_ps f_len_ds f_len_ls f_layers f_init_len
	                f_n_le_N f_rounds_enough f_successors f_i_bound])
	        have f_x_final: "f_x = f_final"
	          using f_fold_res f_final_layer f_final_eq by simp
        have after_trace_nf:
          "None \<notin> dom (dist (execute
            (assert (f_x = f_final) \<bind>
              (\<lambda>_. mfold
                (idx',
                  v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
                (v.receive_query_commits fl) \<bind>
               (\<lambda>(i, x, len, pw). assert (x = final)))) t_trace))"
        proof (rule no_failure_bindI)
          show "None \<notin> dom (dist (execute (assert (f_x = f_final)) t_trace))"
            using f_x_final by (simp add: assert_def)
	        next
	          fix unit_after_assert t_after_assert
	          assume assert_out:
	            "Some (unit_after_assert, t_after_assert) \<in>
	              set_dist (execute (assert (f_x = f_final)) t_trace)"
	          have t_after_assert_eq: "t_after_assert = t_trace"
	            using assert_out f_x_final by (simp add: assert_def)
	          have f_bl_len: "length (butlast (zip f_ls f_ms)) = f_nrounds"
	            using butlast_zip_suc_lengths[OF f_len_ls f_len_ms] f_len_ls f_len_ms
	            by simp
	          have f_drop_empty:
	            "drop f_nrounds (butlast (zip f_ls f_ms)) = []"
	            using f_bl_len by simp
	          have tr_t_trace:
	            "PTranscript t_trace =
	              fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest"
	            using f_fold_res f_drop_empty by simp
	          have t_t_trace: "t \<le> t_trace"
	            by (rule receive_query_commits_mfold_hash_extends[OF f_fold_out])
          have s6_t_trace: "s6 \<le> t_trace"
            using s6_t t_t_trace by (meson p.hash_ext_trans)
          have tr_t_after_assert:
            "PTranscript t_after_assert =
              fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest"
            using t_after_assert_eq tr_t_trace by simp
          have s6_t_after_assert: "s6 \<le> t_after_assert"
            using t_after_assert_eq s6_t_trace by simp
	          have x0_eq:
	            "v.cp_eval as' fv (p.h ^ idx' * shift) = ls ! 0 ! idx'"
	          proof -
	            have raw:
	              "v.cp_eval as' fv (p.h ^ p.index (to_nat idxv) * shift) =
	                ls ! 0 ! p.index (to_nat idxv)"
	              by (rule honest_initial_fri_accumulator_value[
	                  OF htv as_eq _ ls0])
	                (use query_res in simp)
	            show ?thesis
	              using raw idxv_def by simp
	          qed
	          have fold_nf:
	            "None \<notin> dom (dist (execute
	              (mfold
	                (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
	                (v.receive_query_commits fl)) t_after_assert))"
	            unfolding t_after_assert_eq fl_eq
	            by (rule honest_fri_decommitments_mfold_no_failure[
	                OF fri_shape len_ps len_ds len_ls len_ms layers created init_len init_domain
	                  n_le_N len_roots len_challenges roots_aligned successors idx_bound
	                  x0_eq len0_eq tr_t_trace s6_t_trace])
	          show "None \<notin> dom (dist (execute
	            (mfold
	              (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
	              (v.receive_query_commits fl) \<bind>
	             (\<lambda>(i, x, len, pw). assert (x = final))) t_after_assert))"
	          proof (rule no_failure_bindI[OF fold_nf])
	            fix fold_result u
	            assume fold_out:
	              "Some (fold_result, u) \<in>
	                set_dist (execute
	                  (mfold
	                    (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
	                    (v.receive_query_commits fl)) t_after_assert)"
	            obtain i x len pw where fold_eq: "fold_result = (i, x, len, pw)"
	              by (cases fold_result)
	            have fold_out':
	              "Some ((i, x, len, pw), u) \<in>
	                set_dist (execute
	                  (mfold
	                    (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
	                    (v.receive_query_commits fl)) t_after_assert)"
	              using fold_out unfolding fold_eq .
	            have fold_out_zip:
	              "Some ((i, x, len, pw), u) \<in>
	                set_dist (execute
	                  (mfold
	                    (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
	                    (v.receive_query_commits (zip challenges roots))) t_after_assert)"
	              using fold_out' fl_eq by simp
	            have fold_res:
	              "i = idx' mod length (ls ! nrounds) \<and>
	               x = ls ! nrounds ! i \<and>
	               len = length (ls ! nrounds) \<and>
	               pw = 2 ^ nrounds \<and>
	               PTranscript u =
	                 fri_decommitment_transcript i (drop nrounds (butlast (zip ls ms))) @ rest \<and>
	               PState u =
	                 foldl concat (PState t_after_assert)
	                   (fri_decommitment_transcript idx' (butlast (zip ls ms))) \<and>
	               s6 \<le> u"
            by (rule honest_fri_decommitments_mfold_outcome[
                OF fri_shape len_ps len_ds len_ls len_ms layers created init_len init_domain
                  n_le_N len_roots len_challenges roots_aligned successors idx_bound
                  x0_eq len0_eq tr_t_after_assert s6_t_after_assert fold_out_zip])
	            have i_bound: "i < length (ls ! nrounds)"
	            proof -
	              have len_pos: "0 < length (ls ! nrounds)"
	                using fri_commit_outcome_initial_layer_length_power[
	                  OF fri_shape layers init_len n_le_N, of nrounds]
	                by simp
	              then show ?thesis
	                using fold_res by simp
	            qed
	            have final_layer:
	              "ls ! nrounds ! i = hd (last ls)"
	              by (rule honest_fri_final_layer_equals_sent_shape[
	                  OF fri_shape len_ps len_ds len_ls layers init_len n_le_N nrounds_def
	                    successors i_bound])
	            have x_final: "x = final"
	              using fold_res final_layer final_eq by simp
	            show "None \<notin> dom (dist (execute
	              ((case fold_result of (i, x, len, pw) \<Rightarrow> assert (x = final))) u))"
	              unfolding fold_eq using x_final by (simp add: assert_def)
	          qed
	        qed
	        show "None \<notin> dom (dist (execute
	          ((case f_fold_result of (f_i, f_x, f_len, f_pw) \<Rightarrow>
	              assert (f_x = f_final) \<bind>
	              (\<lambda>_. mfold
	                (idx',
	                  v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
	                (v.receive_query_commits fl) \<bind>
	               (\<lambda>(i, x, len, pw). assert (x = final))))) t_trace))"
	          unfolding f_fold_eq using after_trace_nf by simp
	      qed
	    qed
	  qed
	qed

lemma honest_verifier_query_round_outcome_from_state:
  assumes htv: "honest_trace_valid"
    and create_f:
      "Some (f_merkle, s1) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and trace_fri:
      "Some ((f_ps, f_ds, f_ls, f_ms), s_trace_fri) \<in>
        set_dist (execute
          (p.trace_fri_commit f_nrounds [p.f] [p.eval_domain] [p.f_eval]
            [f_merkle]) s2)"
    and f_len_ps: "length f_ps = Suc f_nrounds"
    and f_len_ds: "length f_ds = Suc f_nrounds"
    and f_len_ls: "length f_ls = Suc f_nrounds"
    and f_len_ms: "length f_ms = Suc f_nrounds"
    and f_layers:
      "\<And>i. i < length f_ps \<Longrightarrow> i < length f_ds \<Longrightarrow> i < length f_ls \<Longrightarrow>
        f_ls ! i = map (poly (f_ps ! i)) (f_ds ! i)"
    and f_created:
      "\<And>i. i < length f_ls \<Longrightarrow> i < length f_ms \<Longrightarrow>
        p.created_tree (f_ls ! i) (f_ms ! i) s_trace_fri"
    and f_init_len: "length p.f_eval = 2 ^ FN"
    and f_n_le_N: "f_nrounds \<le> FN"
    and f_nrounds_def: "f_nrounds = ceil_log clength"
    and f_fl_eq: "f_fl = zip f_challenges f_roots"
    and f_final_eq: "f_final = hd (last f_ls)"
    and f_len_roots: "length f_roots = f_nrounds"
    and f_len_challenges: "length f_challenges = f_nrounds"
    and f_roots_aligned: "\<And>j. j < f_nrounds \<Longrightarrow> f_roots ! j = value (f_ms ! j)"
    and f_successors:
      "\<And>j. j < f_nrounds \<Longrightarrow>
        p.next_fri_layer (f_ps ! j) (f_ds ! j) (f_challenges ! j) =
          (f_ps ! Suc j, f_ds ! Suc j, f_ls ! Suc j)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.composition_fri_commit nrounds [cp'] [p.eval_domain]
            [p.cp_eval as] [cp_merkle]) s5)"
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and len_ms: "length ms = Suc nrounds"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and created:
      "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
        p.created_tree (ls ! i) (ms ! i) s6"
    and init_len: "length (p.cp_eval as) = 2 ^ N"
    and n_le_N: "nrounds \<le> N"
    and nrounds_def: "nrounds = ceil_log (degree cp' + 1)"
    and fr_eq: "fr = value f_merkle"
    and as_eq: "as' = as"
    and fl_eq: "fl = zip challenges roots"
    and final_eq: "final = hd (last ls)"
    and len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and roots_aligned: "\<And>j. j < nrounds \<Longrightarrow> roots ! j = value (ms ! j)"
    and successors:
      "\<And>j. j < nrounds \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and lookup: "fmlookup (HashMap s) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some idx"
    and idx_def: "idx' = p.index (to_nat idx)"
    and query_ext: "s1 \<le> s"
    and trace_fri_ext: "s_trace_fri \<le> s"
    and fri_ext: "s6 \<le> s"
    and transcript:
      "PTranscript s =
        query_decommitment_transcript idx' f_merkle @
        fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
        fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest"
    and outcome:
      "Some (res, t') \<in> set_dist (execute (verifier_query_round fr f_fl f_final as' fl final) s)"
  shows
    "PState t' =
      foldl concat (PState s)
        (query_decommitment_transcript idx' f_merkle @
          fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
          fri_decommitment_transcript idx' (butlast (zip ls ms)))"
    "PTranscript t' = rest"
    "s \<le> t'"
proof -
  have f_ls0: "f_ls ! 0 = p.f_eval"
    using trace_fri_commit_initial_heads(3)[OF trace_fri] .
  have f_idx_bound: "idx' < length (f_ls ! 0)"
    using idx_def index_less_domain f_eval_length f_ls0 by simp
  have f_len0_eq: "clength * scale = length (f_ls ! 0)"
    using f_ls0 f_eval_length by simp
  have f_init_domain: "2 ^ FN = clength * scale"
    using f_init_len f_eval_length by simp
  have ls0: "ls ! 0 = p.cp_eval as"
    using composition_fri_commit_initial_heads(3)[OF fri] .
  have idx_bound: "idx' < length (ls ! 0)"
    using idx_def index_less_domain cp_eval_length ls0 by simp
  have len0_eq: "clength * scale = length (ls ! 0)"
    using ls0 cp_eval_length by simp
  have init_domain: "2 ^ N = clength * scale"
    using init_len cp_eval_length by simp
  have trace_fri_shape:
    "fri_commit_outcome f_nrounds p.f p.eval_domain p.f_eval f_merkle
      f_ps f_ds f_ls f_ms s2 s_trace_fri"
    by (rule trace_fri_commit_outcomeI[OF trace_fri])
  have fri_shape:
    "fri_commit_outcome nrounds cp' p.eval_domain (p.cp_eval as) cp_merkle
      ps ds ls ms s5 s6"
    by (rule composition_fri_commit_outcomeI[OF fri])
  have full_eq:
    "verifier_query_round fr f_fl f_final as' fl final =
      (p.receive_query_index_challenge \<bind> (\<lambda>idxv.
        let idxv' = p.index (to_nat idxv) in
        mmap (v.check_decommit_on_query fr idxv') \<bind> (\<lambda>fv.
        mfold
          (idxv', hd fv, clength * scale, 1)
          (v.receive_query_commits f_fl) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pw).
        assert (f_x = f_final) \<bind> (\<lambda>_.
        mfold
          (idxv', v.cp_eval as' fv (p.h ^ idxv' * shift), clength * scale, 1)
          (v.receive_query_commits fl) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    unfolding verifier_query_round_def by (simp add: Let_def sm_bind_assoc split: prod.splits)
  from outcome obtain idxv s_idx fv t f_fold_result t_trace t_after_trace fold_result u where
    rand:
      "Some (idxv, s_idx) \<in> set_dist (execute p.receive_query_index_challenge s)"
    and query_out:
      "Some (fv, t) \<in>
        set_dist (execute
          (mmap (v.check_decommit_on_query fr (p.index (to_nat idxv)))) s_idx)"
    and f_fold_out:
      "Some (f_fold_result, t_trace) \<in>
        set_dist (execute
          (mfold
            (p.index (to_nat idxv), hd fv, clength * scale, 1)
            (v.receive_query_commits f_fl)) t)"
    and f_assert_out:
      "Some ((), t_after_trace) \<in>
        set_dist (execute
          ((case f_fold_result of (f_i, f_x, f_len, f_pw) \<Rightarrow>
              assert (f_x = f_final))) t_trace)"
    and fold_out:
      "Some (fold_result, u) \<in>
        set_dist (execute
          (mfold
            (p.index (to_nat idxv),
              v.cp_eval as' fv (p.h ^ p.index (to_nat idxv) * shift),
              clength * scale, 1)
            (v.receive_query_commits fl)) t_after_trace)"
    and assert_out:
      "Some (res, t') \<in>
        set_dist (execute
          ((case fold_result of (i, x, len, pw) \<Rightarrow> assert (x = final))) u)"
    unfolding full_eq
    by (auto simp: Let_def elim!: p.set_dist_bindE split: prod.splits)
  have rand_res:
    "idxv = idx \<and>
     PState s_idx = PState s \<and>
     PTranscript s_idx = PTranscript s \<and>
     s \<le> s_idx"
    using p.receive_query_index_challenge_known_outcome[OF lookup rand] by simp
  have idxv_def: "p.index (to_nat idxv) = idx'"
    using rand_res idx_def by simp
  have s1_idx: "s1 \<le> s_idx"
    using query_ext rand_res by (meson p.hash_ext_trans)
  have tr_query:
    "PTranscript s_idx =
      query_decommitment_transcript (p.index (to_nat idxv)) f_merkle @
      fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
      fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest"
    using transcript rand_res idxv_def by simp
  have paths:
    "\<And>i. i \<in> set (p.powers_scaled (p.index (to_nat idxv))) \<Longrightarrow>
      length (get_authentication_path (length p.f_eval) i f_merkle) =
        floor_log (length p.f_eval)"
    using query_authentication_path_length[OF create_f] by blast
  have query_out_replay:
    "Some (fv, t) \<in>
      set_dist (execute
        (mmap (v.check_decommit_on_query fr (p.index (to_nat idxv))))
        (s_idx\<lparr>PTranscript :=
          query_decommitment_transcript (p.index (to_nat idxv)) f_merkle @
          fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
          fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest\<rparr>))"
  proof -
    have upd:
      "s_idx\<lparr>PTranscript :=
        query_decommitment_transcript (p.index (to_nat idxv)) f_merkle @
        fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
        fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest\<rparr> =
       s_idx"
      using tr_query by simp
    show ?thesis
      using query_out unfolding upd .
  qed
  have query_res:
    "fv = map (\<lambda>i. p.f_eval ! i) (p.powers_scaled (p.index (to_nat idxv))) \<and>
     PTranscript t =
       fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
       fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest \<and>
     PState t =
       foldl concat (PState s_idx)
         (query_decommitment_transcript (p.index (to_nat idxv)) f_merkle) \<and>
     s_idx\<lparr>PTranscript :=
       query_decommitment_transcript (p.index (to_nat idxv)) f_merkle @
       fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
       fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest\<rparr> \<le> t"
    by (rule honest_query_decommitment_replay_outcome[
        OF paths query_out_replay])
  have s_idx_t: "s_idx \<le> t"
  proof -
    have upd:
      "s_idx\<lparr>PTranscript :=
        query_decommitment_transcript (p.index (to_nat idxv)) f_merkle @
        fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
        fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest\<rparr> =
       s_idx"
      using tr_query by simp
    show ?thesis
      using query_res unfolding upd by simp
  qed
  have s_trace_fri_t: "s_trace_fri \<le> t"
    using trace_fri_ext rand_res s_idx_t by (meson p.hash_ext_trans)
  have tr_t:
    "PTranscript t =
      fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
      fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest"
    using query_res by simp
  have f_x0_eq: "hd fv = f_ls ! 0 ! idx'"
  proof -
    have raw: "hd fv = p.f_eval ! p.index (to_nat idxv)"
      by (rule honest_initial_trace_fri_accumulator_value)
        (use query_res in simp_all)
    show ?thesis
      using raw idxv_def f_ls0 by simp
  qed
  obtain f_i f_x f_len f_pw where f_fold_eq: "f_fold_result = (f_i, f_x, f_len, f_pw)"
    by (cases f_fold_result)
  have f_fold_out':
    "Some ((f_i, f_x, f_len, f_pw), t_trace) \<in>
      set_dist (execute
        (mfold (idx', hd fv, clength * scale, 1)
          (v.receive_query_commits f_fl)) t)"
    using f_fold_out unfolding f_fold_eq idxv_def by simp
  have f_fold_out_zip:
    "Some ((f_i, f_x, f_len, f_pw), t_trace) \<in>
      set_dist (execute
        (mfold (idx', hd fv, clength * scale, 1)
          (v.receive_query_commits (zip f_challenges f_roots))) t)"
    using f_fold_out' f_fl_eq by simp
  have f_fold_res:
    "f_i = idx' mod length (f_ls ! f_nrounds) \<and>
     f_x = f_ls ! f_nrounds ! f_i \<and>
     f_len = length (f_ls ! f_nrounds) \<and>
     f_pw = 2 ^ f_nrounds \<and>
     PTranscript t_trace =
       fri_decommitment_transcript f_i
         (drop f_nrounds (butlast (zip f_ls f_ms))) @
       fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest \<and>
     PState t_trace =
       foldl concat (PState t)
         (fri_decommitment_transcript idx' (butlast (zip f_ls f_ms))) \<and>
    s_trace_fri \<le> t_trace"
    by (rule honest_fri_decommitments_mfold_outcome[
        OF trace_fri_shape f_len_ps f_len_ds f_len_ls f_len_ms f_layers f_created
          f_init_len f_init_domain f_n_le_N f_len_roots f_len_challenges
          f_roots_aligned f_successors f_idx_bound f_x0_eq f_len0_eq
          tr_t s_trace_fri_t f_fold_out_zip])
  have f_i_bound: "f_i < length (f_ls ! f_nrounds)"
  proof -
    have len_pos: "0 < length (f_ls ! f_nrounds)"
      using fri_commit_outcome_initial_layer_length_power[
        OF trace_fri_shape f_layers f_init_len f_n_le_N, of f_nrounds]
      by simp
    then show ?thesis
      using f_fold_res by simp
  qed
  have f_rounds_enough:
    "ceil_log (degree p.f + 1) \<le> f_nrounds"
    using trace_fri_rounds_enough f_nrounds_def by simp
  have f_final_layer:
    "f_ls ! f_nrounds ! f_i = hd (last f_ls)"
    by (rule honest_fri_final_layer_equals_sent_initial_shape[
        OF trace_fri_shape f_len_ps f_len_ds f_len_ls f_layers f_init_len
          f_n_le_N f_rounds_enough f_successors f_i_bound])
  have f_x_final: "f_x = f_final"
    using f_fold_res f_final_layer f_final_eq by simp
  have t_after_trace_eq: "t_after_trace = t_trace"
    using f_assert_out unfolding f_fold_eq f_x_final by (simp add: assert_def)
  have f_bl_len: "length (butlast (zip f_ls f_ms)) = f_nrounds"
    using butlast_zip_suc_lengths[OF f_len_ls f_len_ms] f_len_ls f_len_ms by simp
  have f_drop_empty:
    "drop f_nrounds (butlast (zip f_ls f_ms)) = []"
    using f_bl_len by simp
  have tr_t_after_trace:
    "PTranscript t_after_trace =
      fri_decommitment_transcript idx' (butlast (zip ls ms)) @ rest"
    using f_fold_res f_drop_empty t_after_trace_eq by simp
  have state_t_after_trace:
    "PState t_after_trace =
      foldl concat (PState t)
        (fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)))"
    using f_fold_res t_after_trace_eq by simp
  have s6_t_after_trace: "s6 \<le> t_after_trace"
  proof -
    have t_t_trace: "t \<le> t_trace"
      by (rule receive_query_commits_mfold_hash_extends[OF f_fold_out])
    have t_t_after: "t \<le> t_after_trace"
      using t_after_trace_eq t_t_trace by simp
    show ?thesis
      using fri_ext rand_res s_idx_t t_t_after by (meson p.hash_ext_trans)
  qed
  have t_t_trace_ext: "t \<le> t_trace"
    by (rule receive_query_commits_mfold_hash_extends[OF f_fold_out])
  have x0_eq:
    "v.cp_eval as' fv (p.h ^ idx' * shift) = ls ! 0 ! idx'"
  proof -
    have raw:
      "v.cp_eval as' fv (p.h ^ p.index (to_nat idxv) * shift) =
        ls ! 0 ! p.index (to_nat idxv)"
      by (rule honest_initial_fri_accumulator_value[
          OF htv as_eq _ ls0])
        (use query_res in simp)
    show ?thesis
      using raw idxv_def by simp
  qed
  obtain i x len pw where fold_eq: "fold_result = (i, x, len, pw)"
    by (cases fold_result)
  have fold_out':
    "Some ((i, x, len, pw), u) \<in>
      set_dist (execute
        (mfold
          (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
          (v.receive_query_commits fl)) t_after_trace)"
    using fold_out unfolding fold_eq idxv_def by simp
  have fold_out_zip:
    "Some ((i, x, len, pw), u) \<in>
      set_dist (execute
          (mfold
            (idx', v.cp_eval as' fv (p.h ^ idx' * shift), clength * scale, 1)
            (v.receive_query_commits (zip challenges roots))) t_after_trace)"
    using fold_out' fl_eq by simp
  have fold_res:
    "i = idx' mod length (ls ! nrounds) \<and>
     x = ls ! nrounds ! i \<and>
     len = length (ls ! nrounds) \<and>
     pw = 2 ^ nrounds \<and>
     PTranscript u =
       fri_decommitment_transcript i (drop nrounds (butlast (zip ls ms))) @ rest \<and>
     PState u =
       foldl concat (PState t_after_trace)
         (fri_decommitment_transcript idx' (butlast (zip ls ms))) \<and>
    s6 \<le> u"
    by (rule honest_fri_decommitments_mfold_outcome[
        OF fri_shape len_ps len_ds len_ls len_ms layers created init_len init_domain
          n_le_N len_roots len_challenges roots_aligned successors idx_bound
          x0_eq len0_eq tr_t_after_trace s6_t_after_trace fold_out_zip])
  have i_bound: "i < length (ls ! nrounds)"
  proof -
    have len_pos: "0 < length (ls ! nrounds)"
      using fri_commit_outcome_initial_layer_length_power[
        OF fri_shape layers init_len n_le_N, of nrounds]
      by simp
    then show ?thesis
      using fold_res by simp
  qed
  have final_layer:
    "ls ! nrounds ! i = hd (last ls)"
    by (rule honest_fri_final_layer_equals_sent_shape[
        OF fri_shape len_ps len_ds len_ls layers init_len n_le_N nrounds_def
          successors i_bound])
  have x_final: "x = final"
    using fold_res final_layer final_eq by simp
  have t'_eq: "t' = u"
    using assert_out unfolding fold_eq x_final by (simp add: assert_def)
  have state_query:
    "PState t =
      foldl concat (PState s)
        (query_decommitment_transcript idx' f_merkle)"
    using query_res rand_res idxv_def by simp
  show "PState t' =
    foldl concat (PState s)
      (query_decommitment_transcript idx' f_merkle @
        fri_decommitment_transcript idx' (butlast (zip f_ls f_ms)) @
        fri_decommitment_transcript idx' (butlast (zip ls ms)))"
    using fold_res state_query state_t_after_trace t'_eq by simp
  show "PTranscript t' = rest"
  proof -
    have bl_len: "length (butlast (zip ls ms)) = nrounds"
      using butlast_zip_suc_lengths[OF len_ls len_ms] len_ls len_ms by simp
    have drop_empty: "drop nrounds (butlast (zip ls ms)) = []"
      using bl_len by simp
    show ?thesis
      using fold_res t'_eq drop_empty by simp
  qed
  show "s \<le> t'"
  proof -
    have s_t: "s \<le> t"
      using rand_res s_idx_t by (meson p.hash_ext_trans)
    have t_after_u: "t_after_trace \<le> u"
      by (rule receive_query_commits_mfold_hash_extends[OF fold_out])
    show ?thesis
      using s_t t_t_trace_ext t_after_trace_eq t_after_u t'_eq by (meson p.hash_ext_trans)
	  qed
	qed

lemma verifier_query_round_query_counter:
  assumes outcome:
    "Some (res, t') \<in> set_dist (execute (verifier_query_round fr f_fl f_final as' fl final) s)"
  shows "PQueryCounter t' = Suc (PQueryCounter s)"
proof -
  have full_eq:
    "verifier_query_round fr f_fl f_final as' fl final =
      (p.receive_query_index_challenge \<bind> (\<lambda>idxv.
        let idxv' = p.index (to_nat idxv) in
        mmap (v.check_decommit_on_query fr idxv') \<bind> (\<lambda>fv.
        mfold
          (idxv', hd fv, clength * scale, 1)
          (v.receive_query_commits f_fl) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pw).
        assert (f_x = f_final) \<bind> (\<lambda>_.
        mfold
          (idxv', v.cp_eval as' fv (p.h ^ idxv' * shift), clength * scale, 1)
          (v.receive_query_commits fl) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    unfolding verifier_query_round_def by (simp add: Let_def sm_bind_assoc split: prod.splits)
  from outcome obtain idxv s_idx fv t f_fold_result t_trace t_after_trace fold_result u where
    rand:
      "Some (idxv, s_idx) \<in> set_dist (execute p.receive_query_index_challenge s)"
    and query_out:
      "Some (fv, t) \<in>
        set_dist (execute
          (mmap (v.check_decommit_on_query fr (p.index (to_nat idxv)))) s_idx)"
    and f_fold_out:
      "Some (f_fold_result, t_trace) \<in>
        set_dist (execute
          (mfold
            (p.index (to_nat idxv), hd fv, clength * scale, 1)
            (v.receive_query_commits f_fl)) t)"
    and f_assert_out:
      "Some ((), t_after_trace) \<in>
        set_dist (execute
          ((case f_fold_result of (f_i, f_x, f_len, f_pw) \<Rightarrow>
              assert (f_x = f_final))) t_trace)"
    and fold_out:
      "Some (fold_result, u) \<in>
        set_dist (execute
          (mfold
            (p.index (to_nat idxv),
              v.cp_eval as' fv (p.h ^ p.index (to_nat idxv) * shift),
              clength * scale, 1)
            (v.receive_query_commits fl)) t_after_trace)"
    and assert_out:
      "Some (res, t') \<in>
        set_dist (execute
          ((case fold_result of (i, x, len, pw) \<Rightarrow> assert (x = final))) u)"
    unfolding full_eq
    by (auto simp: Let_def elim!: p.set_dist_bindE split: prod.splits)
  have q_idx: "PQueryCounter s_idx = Suc (PQueryCounter s)"
    using p.receive_query_index_challenge_counter_outcome[OF rand] by simp
  have q_query: "PQueryCounter t = PQueryCounter s_idx"
    by (rule mmap_preserves_query_counter[OF query_out])
      (rule check_decommit_on_query_step_preserves_query_counter)
	  have q_f_fold: "PQueryCounter t_trace = PQueryCounter t"
	    by (rule receive_query_commits_mfold_preserves_query_counter[OF f_fold_out])
	  have q_f_assert: "PQueryCounter t_after_trace = PQueryCounter t_trace"
	  proof -
	    obtain f_i f_x f_len f_pw where f_fold_eq:
	      "f_fold_result = (f_i, f_x, f_len, f_pw)"
	      by (cases f_fold_result)
	    have assert':
	      "Some ((), t_after_trace) \<in>
	        set_dist (execute (assert (f_x = f_final)) t_trace)"
	      using f_assert_out unfolding f_fold_eq by simp
	    show ?thesis
	      using assert_outcomeD(2)[OF assert'] by simp
	  qed
	  have q_fold: "PQueryCounter u = PQueryCounter t_after_trace"
	    by (rule receive_query_commits_mfold_preserves_query_counter[OF fold_out])
	  have q_assert: "PQueryCounter t' = PQueryCounter u"
	  proof -
	    obtain i x len pw where fold_eq: "fold_result = (i, x, len, pw)"
	      by (cases fold_result)
	    have assert':
	      "Some ((), t') \<in> set_dist (execute (assert (x = final)) u)"
	      using assert_out unfolding fold_eq by simp
	    show ?thesis
	      using assert_outcomeD(2)[OF assert'] by simp
	  qed
  show ?thesis
    using q_idx q_query q_f_fold q_f_assert q_fold q_assert by simp
qed

lemma honest_verifier_query_tail_from_prover_tail_no_failure:
  assumes htv: "honest_trace_valid"
    and create_f:
      "Some (f_merkle, s1) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and trace_fri:
      "Some ((f_ps, f_ds, f_ls, f_ms), s_trace_fri) \<in>
        set_dist (execute
          (p.trace_fri_commit f_nrounds [p.f] [p.eval_domain] [p.f_eval]
            [f_merkle]) s2)"
    and f_len_ps: "length f_ps = Suc f_nrounds"
    and f_len_ds: "length f_ds = Suc f_nrounds"
    and f_len_ls: "length f_ls = Suc f_nrounds"
    and f_len_ms: "length f_ms = Suc f_nrounds"
    and f_layers:
      "\<And>i. i < length f_ps \<Longrightarrow> i < length f_ds \<Longrightarrow> i < length f_ls \<Longrightarrow>
        f_ls ! i = map (poly (f_ps ! i)) (f_ds ! i)"
    and f_created:
      "\<And>i. i < length f_ls \<Longrightarrow> i < length f_ms \<Longrightarrow>
        p.created_tree (f_ls ! i) (f_ms ! i) s_trace_fri"
    and f_init_len: "length p.f_eval = 2 ^ FN"
    and f_n_le_N: "f_nrounds \<le> FN"
    and f_nrounds_def: "f_nrounds = ceil_log clength"
    and f_fl_eq: "f_fl = zip f_challenges f_roots"
    and f_final_eq: "f_final = hd (last f_ls)"
    and f_len_roots: "length f_roots = f_nrounds"
    and f_len_challenges: "length f_challenges = f_nrounds"
    and f_roots_aligned: "\<And>j. j < f_nrounds \<Longrightarrow> f_roots ! j = value (f_ms ! j)"
    and f_successors:
      "\<And>j. j < f_nrounds \<Longrightarrow>
        p.next_fri_layer (f_ps ! j) (f_ds ! j) (f_challenges ! j) =
          (f_ps ! Suc j, f_ds ! Suc j, f_ls ! Suc j)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.composition_fri_commit nrounds [cp'] [p.eval_domain]
            [p.cp_eval as] [cp_merkle]) s5)"
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and len_ms: "length ms = Suc nrounds"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and created:
      "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
        p.created_tree (ls ! i) (ms ! i) s6"
    and init_len: "length (p.cp_eval as) = 2 ^ N"
    and n_le_N: "nrounds \<le> N"
    and nrounds_def: "nrounds = ceil_log (degree cp' + 1)"
    and fr_eq: "fr = value f_merkle"
    and as_eq: "as' = as"
    and fl_eq: "fl = zip challenges roots"
    and final_eq: "final = hd (last ls)"
    and len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and roots_aligned: "\<And>j. j < nrounds \<Longrightarrow> roots ! j = value (ms ! j)"
    and successors:
      "\<And>j. j < nrounds \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and tail:
      "Some (prover_result, prover_state) \<in>
        set_dist (execute (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) n) p_s)"
    and state_eq: "PState v_s = PState p_s"
    and transcript_v: "PTranscript v_s = rev ys"
    and transcript_p: "PTranscript prover_state = ys @ PTranscript p_s"
    and prover_ext: "prover_state \<le> v_s"
	    and query_ext: "s1 \<le> v_s"
	    and trace_fri_ext: "s_trace_fri \<le> v_s"
	    and fri_ext: "s6 \<le> v_s"
	    and query_counter_eq: "PQueryCounter v_s = PQueryCounter p_s"
	  shows
	    "None \<notin> dom (dist (execute (ntimes (verifier_query_round fr f_fl f_final as' fl final) n) v_s))"
	  using tail state_eq transcript_v transcript_p prover_ext query_ext trace_fri_ext fri_ext
	    query_counter_eq
	proof (induction n arbitrary: prover_result prover_state p_s v_s ys)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from ntimes_Suc_outcomeE[OF Suc.prems(1)] obtain x xs p_next where
    step:
      "Some (x, p_next) \<in>
        set_dist (execute (prover_query_round f_merkle f_ls f_ms ls ms) p_s)"
    and tail_rest:
      "Some (xs, prover_state) \<in>
        set_dist (execute (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) n) p_next)"
    and prover_result_eq: "prover_result = x # xs"
    by blast
  from prover_query_round_lookup_state_transcript[OF step] obtain idx where
    x_eq: "x = ()"
    and lookup_next: "fmlookup (HashMap p_next) (QueryIndexChallenge (PQueryCounter p_s) (PState p_s)) = Some idx"
	    and state_next:
	      "PState p_next =
	        foldl concat (PState p_s)
	          (query_decommitment_transcript (p.index (to_nat idx)) f_merkle @
	            fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip f_ls f_ms)) @
	            fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip ls ms)))"
	    and tr_next:
	      "PTranscript p_next =
	        rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip ls ms))) @
	        rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip f_ls f_ms))) @
	        rev (query_decommitment_transcript (p.index (to_nat idx)) f_merkle) @
	        PTranscript p_s"
    and p_s_next: "p_s \<le> p_next"
    by blast
	  let ?idx' = "p.index (to_nat idx)"
	  let ?query = "query_decommitment_transcript ?idx' f_merkle"
	  let ?f_fri = "fri_decommitment_transcript ?idx' (butlast (zip f_ls f_ms))"
	  let ?fri = "fri_decommitment_transcript ?idx' (butlast (zip ls ms))"
  have p_next_prover: "p_next \<le> prover_state"
    by (rule ntimes_hash_extends[OF _ tail_rest])
      (rule prover_query_round_hash_extends)
  have p_next_v: "p_next \<le> v_s"
    using p_next_prover Suc.prems(5) by (meson p.hash_ext_trans)
	  have lookup_v: "fmlookup (HashMap v_s) (QueryIndexChallenge (PQueryCounter v_s) (PState v_s)) = Some idx"
	    using p.hash_extension_lookup[OF lookup_next p_next_v] Suc.prems(2) Suc.prems(9)
	    by simp
  have tail_tr_ext: "transcript_extends prover_state p_next"
    by (rule ntimes_transcript_extends[OF _ tail_rest])
      (rule prover_query_round_transcript_extends)
  from tail_tr_ext obtain ys_tail where
    tr_tail: "PTranscript prover_state = ys_tail @ PTranscript p_next"
    unfolding transcript_extends_def by auto
	  have ys_eq: "ys = ys_tail @ rev ?fri @ rev ?f_fri @ rev ?query"
	    using Suc.prems(4) tr_tail tr_next by simp
	  have transcript_round:
	    "PTranscript v_s = ?query @ ?f_fri @ ?fri @ rev ys_tail"
	    using Suc.prems(3) ys_eq by simp
	  have step_nf:
	    "None \<notin> dom (dist (execute (verifier_query_round fr f_fl f_final as' fl final) v_s))"
	    by (rule honest_verifier_query_round_no_failure_from_state[
	        OF htv create_f trace_fri f_len_ps f_len_ds f_len_ls f_len_ms f_layers
	          f_created f_init_len f_n_le_N f_nrounds_def f_fl_eq f_final_eq
	          f_len_roots f_len_challenges f_roots_aligned f_successors
	          fri len_ps len_ds len_ls len_ms layers created init_len n_le_N
	          nrounds_def fr_eq as_eq fl_eq final_eq len_roots len_challenges
	          roots_aligned successors lookup_v refl Suc.prems(6) Suc.prems(7) Suc.prems(8)
	          transcript_round])
  show ?case
    unfolding ntimes.simps
  proof (rule no_failure_bindI[OF step_nf])
    fix v_res v_next
    assume v_step:
      "Some (v_res, v_next) \<in>
        set_dist (execute (verifier_query_round fr f_fl f_final as' fl final) v_s)"
		    have v_state:
		      "PState v_next =
		        foldl concat (PState v_s) (?query @ ?f_fri @ ?fri)"
		      by (rule honest_verifier_query_round_outcome_from_state(1)[
		          OF htv create_f trace_fri f_len_ps f_len_ds f_len_ls f_len_ms f_layers
		            f_created f_init_len f_n_le_N f_nrounds_def f_fl_eq f_final_eq
		            f_len_roots f_len_challenges f_roots_aligned f_successors
		            fri len_ps len_ds len_ls len_ms layers created init_len n_le_N
		            nrounds_def fr_eq as_eq fl_eq final_eq len_roots len_challenges
		            roots_aligned successors lookup_v refl Suc.prems(6) Suc.prems(7) Suc.prems(8)
		            transcript_round v_step])
	    have v_transcript: "PTranscript v_next = rev ys_tail"
		      by (rule honest_verifier_query_round_outcome_from_state(2)[
		          OF htv create_f trace_fri f_len_ps f_len_ds f_len_ls f_len_ms f_layers
		            f_created f_init_len f_n_le_N f_nrounds_def f_fl_eq f_final_eq
		            f_len_roots f_len_challenges f_roots_aligned f_successors
		            fri len_ps len_ds len_ls len_ms layers created init_len n_le_N
		            nrounds_def fr_eq as_eq fl_eq final_eq len_roots len_challenges
		            roots_aligned successors lookup_v refl Suc.prems(6) Suc.prems(7) Suc.prems(8)
		            transcript_round v_step])
	    have v_ext: "v_s \<le> v_next"
		      by (rule honest_verifier_query_round_outcome_from_state(3)[
		          OF htv create_f trace_fri f_len_ps f_len_ds f_len_ls f_len_ms f_layers
		            f_created f_init_len f_n_le_N f_nrounds_def f_fl_eq f_final_eq
		            f_len_roots f_len_challenges f_roots_aligned f_successors
		            fri len_ps len_ds len_ls len_ms layers created init_len n_le_N
		            nrounds_def fr_eq as_eq fl_eq final_eq len_roots len_challenges
		            roots_aligned successors lookup_v refl Suc.prems(6) Suc.prems(7) Suc.prems(8)
		            transcript_round v_step])
    have state_v_next: "PState v_next = PState p_next"
      using v_state state_next Suc.prems(2) by simp
    have prover_ext_next: "prover_state \<le> v_next"
      using Suc.prems(5) v_ext by (meson p.hash_ext_trans)
	    have query_ext_next: "s1 \<le> v_next"
	      using Suc.prems(6) v_ext by (meson p.hash_ext_trans)
	    have trace_fri_ext_next: "s_trace_fri \<le> v_next"
	      using Suc.prems(7) v_ext by (meson p.hash_ext_trans)
		    have fri_ext_next: "s6 \<le> v_next"
		      using Suc.prems(8) v_ext by (meson p.hash_ext_trans)
	    have q_p_next: "PQueryCounter p_next = Suc (PQueryCounter p_s)"
	      by (rule prover_query_round_query_counter[OF step])
	    have q_v_next: "PQueryCounter v_next = Suc (PQueryCounter v_s)"
	      by (rule verifier_query_round_query_counter[OF v_step])
	    have query_counter_next: "PQueryCounter v_next = PQueryCounter p_next"
	      using q_p_next q_v_next Suc.prems(9) by simp
	    have tail_nf:
	      "None \<notin> dom
	        (dist (execute (ntimes (verifier_query_round fr f_fl f_final as' fl final) n) v_next))"
		      by (rule Suc.IH[
		          OF tail_rest state_v_next v_transcript tr_tail prover_ext_next
		            query_ext_next trace_fri_ext_next fri_ext_next query_counter_next])
    show "None \<notin> dom (dist (execute
      (ntimes (verifier_query_round fr f_fl f_final as' fl final) n \<bind>
        (\<lambda>xs. return (v_res # xs))) v_next))"
      by (rule no_failure_bind_returnI[OF tail_nf])
  qed
qed

lemma honest_verify_from_prover_no_failure:
  assumes htv: "honest_trace_valid"
    and prover:
      "Some (prover_result, prover_state) \<in>
        set_dist (execute p.prover_monad init_state)"
    and replay: "replay_state = verifier_replay_state prover_state"
  shows "None \<notin> dom (dist (execute v.verify_monad replay_state))"
proof (rule honest_prover_monad_outcome[OF prover])
  fix f_merkle s1 s2 f_nrounds f_ps f_ds f_ls f_ms s_trace_fri
      s_trace_final as s3 cp' s4 cp_merkle s5 nrounds ps ds ls ms s6 s_final
  assume create_f:
        "Some (f_merkle, s1) \<in>
          set_dist (execute (p.create p.f_eval) init_state)"
    and created_f: "p.created_tree p.f_eval f_merkle s1"
    and send_f:
        "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
    and f_nrounds_def: "f_nrounds = ceil_log clength"
    and trace_fri:
        "Some ((f_ps, f_ds, f_ls, f_ms), s_trace_fri) \<in>
          set_dist (execute
            (p.trace_fri_commit f_nrounds [p.f] [p.eval_domain] [p.f_eval]
              [f_merkle]) s2)"
    and f_len_ps: "length f_ps = Suc f_nrounds"
    and f_len_ds: "length f_ds = Suc f_nrounds"
    and f_len_ls: "length f_ls = Suc f_nrounds"
    and f_len_ms: "length f_ms = Suc f_nrounds"
    and f_layers:
        "\<And>i. i < length f_ps \<Longrightarrow> i < length f_ds \<Longrightarrow> i < length f_ls \<Longrightarrow>
          f_ls ! i = map (poly (f_ps ! i)) (f_ds ! i)"
    and f_created:
        "\<And>i. i < length f_ls \<Longrightarrow> i < length f_ms \<Longrightarrow>
          p.created_tree (f_ls ! i) (f_ms ! i) s_trace_fri"
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
    and created_cp: "p.created_tree (p.cp_eval as) cp_merkle s5"
    and nrounds_def: "nrounds = ceil_log (degree cp' + 1)"
    and fri:
        "Some ((ps, ds, ls, ms), s6) \<in>
          set_dist (execute
            (p.composition_fri_commit nrounds [cp'] [p.eval_domain]
              [p.cp_eval as] [cp_merkle]) s5)"
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and len_ms: "length ms = Suc nrounds"
    and layers:
        "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
          ls ! i = map (poly (ps ! i)) (ds ! i)"
    and created:
        "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
          p.created_tree (ls ! i) (ms ! i) s6"
    and final_send:
        "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    and tail:
        "Some (prover_result, prover_state) \<in>
          set_dist (execute
            (ntimes (prover_query_round f_merkle f_ls f_ms ls ms) rounds) s_final)"
  from cp_eval_length_power obtain N where init_len:
    "length (p.cp_eval as) = 2 ^ N"
    by blast
  have n_le_N: "nrounds \<le> N"
    by (rule fri_rounds_le_eval_domain_log[OF htv cp'_def nrounds_def init_len])
  from f_eval_length_power obtain FN where f_init_len:
    "length p.f_eval = 2 ^ FN"
    by blast
  have f_n_le_N: "f_nrounds \<le> FN"
  proof -
    have cl_le_len: "clength \<le> length p.f_eval"
      using f_eval_length p.scale_pos by simp
    have f_rounds_le_len: "f_nrounds \<le> ceil_log (length p.f_eval)"
      using ceil_log_mono[OF cl_le_len] f_nrounds_def by simp
    have len_pos: "0 < length p.f_eval"
      using f_init_len by simp
    have ceil_len_le: "ceil_log (length p.f_eval) \<le> FN"
    proof -
      have "length p.f_eval - 1 < 2 ^ FN"
        using f_init_len len_pos by simp
      then have "ceil_log (Suc (length p.f_eval - 1)) \<le> FN"
        by (rule ceil_log_Suc_le_power)
      then show ?thesis
        using len_pos by simp
    qed
    show ?thesis
      using f_rounds_le_len ceil_len_le by simp
  qed
  from trace_fri_commit_initial_replay_successor_data[OF trace_fri]
  obtain f_roots f_challenges where
    f_len_roots: "length f_roots = f_nrounds"
    and f_len_challenges: "length f_challenges = f_nrounds"
    and f_roots_aligned: "\<forall>j < f_nrounds. f_roots ! j = value (f_ms ! j)"
    and f_successors:
      "\<forall>j < f_nrounds.
        p.next_fri_layer (f_ps ! j) (f_ds ! j) (f_challenges ! j) =
          (f_ps ! Suc j, f_ds ! Suc j, f_ls ! Suc j)"
    by blast
  from composition_fri_commit_initial_replay_successor_data[OF fri]
  obtain roots challenges where
    len_roots: "length roots = nrounds"
    and len_challenges: "length challenges = nrounds"
    and roots_aligned: "\<forall>j < nrounds. roots ! j = value (ms ! j)"
    and successors:
      "\<forall>j < nrounds.
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
	    by blast
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
		      f_fl \<leftarrow> ntimes v.receive_trace_fri_commits (ceil_log clength);
		      f_final \<leftarrow> p.read;
		      as' \<leftarrow> mmap (replicate (length spec) ?round);
		      dg \<leftarrow> p.read;
		      assert (to_nat dg \<le> p.maxDegree);
		      fl \<leftarrow> ntimes v.receive_composition_fri_commits
		        (ceil_log (to_nat dg + 1));
		      final \<leftarrow> p.read;
		      return (fr, f_fl, f_final, as', dg, fl, final)
		    }"
		  have prefix_nf:
		    "None \<notin> dom (dist (execute ?prefix replay_state))"
	    by (rule honest_trace_root_alpha_degree_fri_final_dynamic_from_prover_tail_no_failure[
	        OF htv create_f send_f f_nrounds_def trace_fri trace_final_send alphas
	          cp'_def send_degree create_cp nrounds_def fri final_send tail replay])
	  have full_eq:
	    "v.verify_monad =
	      (?prefix \<bind>
	        (\<lambda>out. case out of (fr, f_fl, f_final, as', dg, fl, final) \<Rightarrow>
	          ntimes (verifier_query_round fr f_fl f_final as' fl final) rounds))"
	    unfolding v.verify_monad_def
	    by (simp add: Let_def verifier_query_round_def sm_bind_assoc split: prod.splits)
	  show ?thesis
	    unfolding full_eq
	  proof (rule no_failure_bindI[OF prefix_nf])
	    fix out t
	    assume prefix_out_raw: "Some (out, t) \<in> set_dist (execute ?prefix replay_state)"
	    obtain fr f_fl f_final as' dg fl final where out_eq:
	      "out = (fr, f_fl, f_final, as', dg, fl, final)"
	      by (cases out) auto
		    show "None \<notin> dom (dist (execute
		      ((case out of (fr, f_fl, f_final, as', dg, fl, final) \<Rightarrow>
		        ntimes (verifier_query_round fr f_fl f_final as' fl final) rounds)) t))"
		    proof -
		      have prefix_out:
		        "Some ((fr, f_fl, f_final, as', dg, fl, final), t) \<in>
		          set_dist (execute ?prefix replay_state)"
		        using prefix_out_raw unfolding out_eq .
		      obtain f_roots0 f_challenges0 roots0 challenges0 ys where
		        f_len_roots0: "length f_roots0 = f_nrounds"
		        and f_len_challenges0: "length f_challenges0 = f_nrounds"
		        and f_fl_eq0: "f_fl = zip f_challenges0 f_roots0"
		        and f_roots_aligned0:
		          "\<And>j. j < f_nrounds \<Longrightarrow> f_roots0 ! j = value (f_ms ! j)"
		        and f_successors0:
		          "\<And>j. j < f_nrounds \<Longrightarrow>
		            p.next_fri_layer (f_ps ! j) (f_ds ! j) (f_challenges0 ! j) =
		              (f_ps ! Suc j, f_ds ! Suc j, f_ls ! Suc j)"
		        and f_final_eq: "f_final = hd (last f_ls)"
		        and
		        len_roots0: "length roots0 = nrounds"
		        and len_challenges0: "length challenges0 = nrounds"
		        and fl_eq0: "fl = zip challenges0 roots0"
		        and roots_aligned0:
		          "\<And>j. j < nrounds \<Longrightarrow> roots0 ! j = value (ms ! j)"
		        and successors0:
		          "\<And>j. j < nrounds \<Longrightarrow>
		            p.next_fri_layer (ps ! j) (ds ! j) (challenges0 ! j) =
		              (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
		        and fr_eq: "fr = value f_merkle"
		        and as_eq: "as' = as"
		        and dg_eq: "dg = of_nat (degree (p.cp as p.f_powers))"
		        and final_eq: "final = hd (last ls)"
		        and state_t: "PState t = PState s_final"
		        and transcript_t: "PTranscript t = rev ys"
		        and transcript_prover:
		          "PTranscript prover_state = ys @ PTranscript s_final"
		        and replay_t: "replay_state \<le> t"
		        using honest_trace_root_alpha_degree_fri_final_dynamic_from_prover_tail_outcome[
		            OF htv create_f send_f f_nrounds_def trace_fri trace_final_send alphas
		              cp'_def send_degree create_cp nrounds_def fri final_send tail replay prefix_out]
		        by blast
		      have tail_hash: "s_final \<le> prover_state"
		        by (rule ntimes_hash_extends[OF _ tail])
		          (rule prover_query_round_hash_extends)
		      have prover_replay: "prover_state \<le> replay_state"
		        using replay
		        unfolding verifier_replay_state_def less_eq_hash_ext_def less_eq_fmap_def
		        by simp
		      have prover_t: "prover_state \<le> t"
		        using prover_replay replay_t by (meson p.hash_ext_trans)
			      have alpha_data:
			        "length as = length spec \<and>
			         s_trace_final \<le> s3 \<and>
			         PState s3 = foldl concat (PState s_trace_final) as \<and>
			         PTranscript s3 = rev as @ PTranscript s_trace_final \<and>
			         PTraceFriCounter s3 = PTraceFriCounter s_trace_final \<and>
			         PCompositionFriCounter s3 = PCompositionFriCounter s_trace_final \<and>
			         PAlphaCounter s3 = PAlphaCounter s_trace_final + length as \<and>
			         PQueryCounter s3 = PQueryCounter s_trace_final \<and>
			         (\<forall>i < length as.
			            fmlookup (HashMap s3)
			              (AlphaChallenge (PAlphaCounter s_trace_final + i)
			                (foldl concat (PState s_trace_final) (take i as))) =
			              Some (as ! i))"
			        using alpha_mmap_outcome[OF alphas] by simp
		      have s1_s2: "s1 \<le> s2"
		        using send_hash_extends[OF send_f] .
		      have s2_trace_fri: "s2 \<le> s_trace_fri"
		        using p.trace_fri_commit_extends[OF trace_fri] .
		      have trace_fri_final: "s_trace_fri \<le> s_trace_final"
		        using send_hash_extends[OF trace_final_send] .
		      have trace_final_s3: "s_trace_final \<le> s3"
		        using alpha_data by simp
		      have s3_s4: "s3 \<le> s4"
		        using send_hash_extends[OF send_degree] .
		      have s4_s5: "s4 \<le> s5"
		        using create_hash_extends[OF create_cp] .
		      have s5_s6: "s5 \<le> s6"
		        using p.composition_fri_commit_extends[OF fri] .
		      have s6_final_hash: "s6 \<le> s_final"
		        using send_hash_extends[OF final_send] .
		      have s1_prover: "s1 \<le> prover_state"
		        using s1_s2 s2_trace_fri trace_fri_final trace_final_s3
		          s3_s4 s4_s5 s5_s6 s6_final_hash tail_hash
		        by (meson p.hash_ext_trans)
		      have trace_fri_prover: "s_trace_fri \<le> prover_state"
		        using trace_fri_final trace_final_s3 s3_s4 s4_s5 s5_s6
		          s6_final_hash tail_hash
		        by (meson p.hash_ext_trans)
		      have s6_prover: "s6 \<le> prover_state"
		        using s6_final_hash tail_hash by (rule p.hash_ext_trans)
		      have s1_t: "s1 \<le> t"
		        using s1_prover prover_t by (meson p.hash_ext_trans)
		      have s_trace_fri_t: "s_trace_fri \<le> t"
		        using trace_fri_prover prover_t by (meson p.hash_ext_trans)
			      have s6_t: "s6 \<le> t"
			        using s6_prover prover_t by (meson p.hash_ext_trans)
			      have q_t_replay: "PQueryCounter t = PQueryCounter replay_state"
			        by (rule honest_trace_root_alpha_degree_fri_final_dynamic_prefix_preserves_query_counter[
			            OF prefix_out])
			      have q_s1_zero: "PQueryCounter s1 = 0"
			        using p.create_preserves_channel(6)[OF create_f]
			        unfolding init_state_def by simp
			      have q_s2_zero: "PQueryCounter s2 = 0"
			        using p.send_outcome[OF send_f] q_s1_zero by simp
			      have q_trace_fri_zero: "PQueryCounter s_trace_fri = 0"
			        using trace_fri_commit_preserves_query_counter[OF trace_fri] q_s2_zero
			        by simp
			      have q_trace_final_zero: "PQueryCounter s_trace_final = 0"
			        using p.send_outcome[OF trace_final_send] q_trace_fri_zero by simp
			      have q_s3_zero: "PQueryCounter s3 = 0"
			        using alpha_data q_trace_final_zero by simp
			      have q_s4_zero: "PQueryCounter s4 = 0"
			        using p.send_outcome[OF send_degree] q_s3_zero by simp
			      have q_s5_zero: "PQueryCounter s5 = 0"
			        using p.create_preserves_channel(6)[OF create_cp] q_s4_zero by simp
			      have q_s6_zero: "PQueryCounter s6 = 0"
			        using composition_fri_commit_preserves_query_counter[OF fri] q_s5_zero
			        by simp
			      have q_s_final_zero: "PQueryCounter s_final = 0"
			        using p.send_outcome[OF final_send] q_s6_zero by simp
			      have query_counter_t_final: "PQueryCounter t = PQueryCounter s_final"
			        using q_t_replay q_s_final_zero replay
			        unfolding verifier_replay_state_def by simp
			      have tail_nf:
			        "None \<notin> dom
			          (dist (execute (ntimes (verifier_query_round fr f_fl f_final as' fl final) rounds) t))"
		        by (rule honest_verifier_query_tail_from_prover_tail_no_failure[
		            OF htv create_f trace_fri f_len_ps f_len_ds f_len_ls f_len_ms f_layers
		              f_created f_init_len f_n_le_N f_nrounds_def f_fl_eq0 f_final_eq
		              f_len_roots0 f_len_challenges0 f_roots_aligned0 f_successors0
		              fri len_ps len_ds len_ls len_ms layers created init_len n_le_N
			              nrounds_def fr_eq as_eq fl_eq0 final_eq len_roots0 len_challenges0
			              roots_aligned0 successors0 tail state_t transcript_t transcript_prover
			              prover_t s1_t s_trace_fri_t s6_t query_counter_t_final])
		      show ?thesis
		        unfolding out_eq using tail_nf by simp
		    qed
		  qed
		qed

lemma honest_trace_valid_implies_no_failure:
  assumes htv: "honest_trace_valid"
  shows "None \<notin> dom (dist (execute exec init_state))"
  unfolding exec_def
proof (rule no_failure_bindI[OF prover_monad_no_failure])
  fix prover_result prover_state
  assume prover:
    "Some (prover_result, prover_state) \<in>
      set_dist (execute p.prover_monad init_state)"
  show "None \<notin> dom (dist (execute
    (modify (\<lambda>c. c\<lparr>PState := 0, PTranscript := rev (PTranscript c),
      PTraceFriCounter := 0, PCompositionFriCounter := 0,
      PAlphaCounter := 0, PQueryCounter := 0\<rparr>) \<bind>
      (\<lambda>_. v.verify_monad))
    prover_state))"
  proof (rule no_failure_bindI)
    show "None \<notin> dom (dist (execute
      (modify (\<lambda>c. c\<lparr>PState := 0, PTranscript := rev (PTranscript c),
        PTraceFriCounter := 0, PCompositionFriCounter := 0,
        PAlphaCounter := 0, PQueryCounter := 0\<rparr>))
      prover_state))"
      by simp
  next
    fix u replay_state
    assume reset:
      "Some (u, replay_state) \<in>
        set_dist (execute
          (modify (\<lambda>c. c\<lparr>PState := 0, PTranscript := rev (PTranscript c),
            PTraceFriCounter := 0, PCompositionFriCounter := 0,
            PAlphaCounter := 0, PQueryCounter := 0\<rparr>))
          prover_state)"
    have replay: "replay_state = verifier_replay_state prover_state"
      using modify_verifier_replay_state_outcome[OF reset] by simp
    show "None \<notin> dom (dist (execute v.verify_monad replay_state))"
      by (rule honest_verify_from_prover_no_failure[OF htv prover replay])
  qed
qed

lemma honest_query_decommitments_no_fail:
  assumes "honest_trace_valid"
  shows "no_failure exec init_state"
  using honest_trace_valid_implies_no_failure[OF assms]
  unfolding no_failure_def .

lemma honest_fri_decommitments_no_fail:
  assumes "honest_trace_valid"
  shows "no_failure exec init_state"
  using honest_trace_valid_implies_no_failure[OF assms]
  unfolding no_failure_def .

lemma honest_final_constant_no_fail:
  assumes "honest_trace_valid"
  shows "no_failure exec init_state"
  using honest_trace_valid_implies_no_failure[OF assms]
  unfolding no_failure_def .

lemma honest_verify_no_fail:
  assumes "honest_trace_valid"
  shows "no_failure exec init_state"
  using honest_trace_valid_implies_no_failure[OF assms]
  unfolding no_failure_def .

lemma wp_event_is_none_eq_wp_error:
  "wp_event m (\<lambda>a. Option.is_none a) s = wp_error m s"
  unfolding wp_event_def wp_error_def
  by (rule arg_cong[where f="\<lambda>Q. wp m Q s"]) (auto intro!: ext split: option.splits)

lemma wp_error_zero_if_no_failure:
  assumes "None \<notin> dom (dist (execute m s))"
  shows "wp_error m s = 0"
proof -
  have "failure_prob m s = 0"
    using assms
    unfolding failure_prob_def
    by (cases "dist (execute m s) None") (auto simp: domIff)
  then show ?thesis
    by (simp add: wp_error_eq_failure_prob)
qed

lemma completeness_wp_reduction:
  assumes "honest_trace_valid"
  shows "wp_event exec (\<lambda>a. Option.is_none a) init_state = 0"
  using honest_trace_valid_implies_no_failure[OF assms]
  by (simp add: wp_event_is_none_eq_wp_error wp_error_zero_if_no_failure)

lemma completeness:
  assumes "honest_trace_valid"
  shows "wp_event exec (\<lambda>a. Option.is_none a) init_state \<le> (0::prob)"
  using completeness_wp_reduction[OF assms]
  by simp

end

end
