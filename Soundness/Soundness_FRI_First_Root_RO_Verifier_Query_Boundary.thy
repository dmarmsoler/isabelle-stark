(*  Title:      Stark/Soundness_FRI_First_Root_RO_Verifier_Query_Boundary.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_Verifier_Query_Boundary
  imports Soundness_FRI_First_Root_RO_Actual_Agreement
begin


context soundness
begin

lemma ro_receive_trace_fri_commits_outcome_parse:
  fixes s t :: "'f protocol_channel"
    and root root' b :: 'f
    and rest :: "'f list"
  assumes tr: "PTranscript s = root # rest"
    and outcome:
      "Some ((b, root'), t) \<in>
        set_dist (execute ro_receive_trace_fri_commits s)"
  shows
    "root' = root \<and>
     PTranscript t = rest \<and>
     s \<le> t \<and>
     PQueryCounter t = PQueryCounter s"
proof -
  from outcome obtain s1 where
    read:
      "Some (root', s1) \<in> set_dist (execute protocol_absorb_read s)"
    and challenge:
      "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s1)"
    unfolding ro_receive_trace_fri_commits_def
      ro_receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  from protocol_absorb_read_outcome_with_lookup_chain[OF read]
  obtain xs where
    tr_s: "PTranscript s = root' # xs"
    and tr_s1: "PTranscript s1 = xs"
    and ext_s1: "s \<le> s1"
    and counter_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  have root_eq: "root' = root" and xs_eq: "xs = rest"
    using tr tr_s by simp_all
  have challenge_props:
    "s1 \<le> t \<and>
     PTranscript t = PTranscript s1"
    using receive_trace_fri_challenge_outcome[OF challenge] by blast
  have counter_t: "PQueryCounter t = PQueryCounter s1"
    using receive_trace_fri_challenge_counter_outcome[OF challenge] by simp
  have ext: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s1])
      (use challenge_props in simp)
  show ?thesis
    using root_eq xs_eq tr_s1 challenge_props counter_s1 counter_t ext
    by simp
qed

lemma ro_receive_composition_fri_commits_outcome_parse:
  fixes s t :: "'f protocol_channel"
    and root root' b :: 'f
    and rest :: "'f list"
  assumes tr: "PTranscript s = root # rest"
    and outcome:
      "Some ((b, root'), t) \<in>
        set_dist (execute ro_receive_composition_fri_commits s)"
  shows
    "root' = root \<and>
     PTranscript t = rest \<and>
     s \<le> t \<and>
     PQueryCounter t = PQueryCounter s"
proof -
  from outcome obtain s1 where
    read:
      "Some (root', s1) \<in> set_dist (execute protocol_absorb_read s)"
    and challenge:
      "Some (b, t) \<in>
        set_dist (execute receive_composition_fri_challenge s1)"
    unfolding ro_receive_composition_fri_commits_def
      ro_receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  from protocol_absorb_read_outcome_with_lookup_chain[OF read]
  obtain xs where
    tr_s: "PTranscript s = root' # xs"
    and tr_s1: "PTranscript s1 = xs"
    and ext_s1: "s \<le> s1"
    and counter_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  have root_eq: "root' = root" and xs_eq: "xs = rest"
    using tr tr_s by simp_all
  have challenge_props:
    "s1 \<le> t \<and>
     PTranscript t = PTranscript s1"
    using receive_composition_fri_challenge_outcome[OF challenge] by blast
  have counter_t: "PQueryCounter t = PQueryCounter s1"
    using receive_composition_fri_challenge_counter_outcome[OF challenge]
    by simp
  have ext: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s1])
      (use challenge_props in simp)
  show ?thesis
    using root_eq xs_eq tr_s1 challenge_props counter_s1 counter_t ext
    by simp
qed

lemma ntimes_ro_receive_trace_fri_commits_outcome_parse:
  fixes s t :: "'f protocol_channel"
    and roots rest :: "'f list"
  assumes tr: "PTranscript s = roots @ rest"
    and roots_len: "length roots = n"
    and outcome:
      "Some (pairs, t) \<in>
        set_dist (execute (ntimes ro_receive_trace_fri_commits n) s)"
  shows
    "map snd pairs = roots \<and>
     PTranscript t = rest \<and>
     s \<le> t \<and>
     PQueryCounter t = PQueryCounter s"
  using roots_len tr outcome
proof (induction n arbitrary: s roots pairs t)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems(1) obtain root roots_tail where
    roots_eq: "roots = root # roots_tail"
    and roots_tail_len: "length roots_tail = n"
    by (cases roots) auto
  from Suc.prems(3) obtain b root' s1 pairs_tail where
    head:
      "Some ((b, root'), s1) \<in>
        set_dist (execute ro_receive_trace_fri_commits s)"
    and tail:
      "Some (pairs_tail, t) \<in>
        set_dist (execute (ntimes ro_receive_trace_fri_commits n) s1)"
    and pairs_eq: "pairs = (b, root') # pairs_tail"
    by (auto elim!: set_dist_bindE split: prod.splits)
  have tr_head: "PTranscript s = root # (roots_tail @ rest)"
    using Suc.prems(2) roots_eq by simp
  have head_props:
    "root' = root \<and>
     PTranscript s1 = roots_tail @ rest \<and>
     s \<le> s1 \<and>
     PQueryCounter s1 = PQueryCounter s"
    by (rule ro_receive_trace_fri_commits_outcome_parse[
          OF tr_head head])
  have tail_props:
    "map snd pairs_tail = roots_tail \<and>
     PTranscript t = rest \<and>
     s1 \<le> t \<and>
     PQueryCounter t = PQueryCounter s1"
    by (rule Suc.IH[OF roots_tail_len _ tail])
      (use head_props in simp)
  have ext: "s \<le> t"
    using head_props tail_props by (meson hash_ext_trans)
  show ?case
    using roots_eq pairs_eq head_props tail_props ext by simp
qed

lemma ntimes_ro_receive_composition_fri_commits_outcome_parse:
  fixes s t :: "'f protocol_channel"
    and roots rest :: "'f list"
  assumes tr: "PTranscript s = roots @ rest"
    and roots_len: "length roots = n"
    and outcome:
      "Some (pairs, t) \<in>
        set_dist
          (execute (ntimes ro_receive_composition_fri_commits n) s)"
  shows
    "map snd pairs = roots \<and>
     PTranscript t = rest \<and>
     s \<le> t \<and>
     PQueryCounter t = PQueryCounter s"
  using roots_len tr outcome
proof (induction n arbitrary: s roots pairs t)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems(1) obtain root roots_tail where
    roots_eq: "roots = root # roots_tail"
    and roots_tail_len: "length roots_tail = n"
    by (cases roots) auto
  from Suc.prems(3) obtain b root' s1 pairs_tail where
    head:
      "Some ((b, root'), s1) \<in>
        set_dist (execute ro_receive_composition_fri_commits s)"
    and tail:
      "Some (pairs_tail, t) \<in>
        set_dist
          (execute (ntimes ro_receive_composition_fri_commits n) s1)"
    and pairs_eq: "pairs = (b, root') # pairs_tail"
    by (auto elim!: set_dist_bindE split: prod.splits)
  have tr_head: "PTranscript s = root # (roots_tail @ rest)"
    using Suc.prems(2) roots_eq by simp
  have head_props:
    "root' = root \<and>
     PTranscript s1 = roots_tail @ rest \<and>
     s \<le> s1 \<and>
     PQueryCounter s1 = PQueryCounter s"
    by (rule ro_receive_composition_fri_commits_outcome_parse[
          OF tr_head head])
  have tail_props:
    "map snd pairs_tail = roots_tail \<and>
     PTranscript t = rest \<and>
     s1 \<le> t \<and>
     PQueryCounter t = PQueryCounter s1"
    by (rule Suc.IH[OF roots_tail_len _ tail])
      (use head_props in simp)
  have ext: "s \<le> t"
    using head_props tail_props by (meson hash_ext_trans)
  show ?case
    using roots_eq pairs_eq head_props tail_props ext by simp
qed

lemma ro_alpha_round_outcome_parse:
  fixes s t :: "'f protocol_channel"
    and a a' :: 'f
    and rest :: "'f list"
  assumes tr: "PTranscript s = a # rest"
    and outcome: "Some (a', t) \<in> set_dist (execute ro_alpha_round s)"
  shows
    "a' = a \<and>
     PTranscript t = rest \<and>
     s \<le> t \<and>
     PQueryCounter t = PQueryCounter s"
proof -
  from outcome obtain a0 s1 a1 s2 where
    challenge:
      "Some (a0, s1) \<in> set_dist (execute receive_alpha_challenge s)"
    and read:
      "Some (a1, s2) \<in> set_dist (execute protocol_absorb_read s1)"
    and assert:
      "Some ((), t) \<in> set_dist (execute (assert (a0 = a1)) s2)"
    and a'_eq: "a' = a1"
    unfolding ro_alpha_round_def
    by (auto elim!: set_dist_bindE)
  have challenge_props:
    "s \<le> s1 \<and>
     PTranscript s1 = PTranscript s"
    using receive_alpha_challenge_outcome[OF challenge] by blast
  have challenge_counter: "PQueryCounter s1 = PQueryCounter s"
    using receive_alpha_challenge_counter_outcome[OF challenge] by simp
  from protocol_absorb_read_outcome_with_lookup_chain[OF read]
  obtain xs where
    tr_s1: "PTranscript s1 = a1 # xs"
    and tr_s2: "PTranscript s2 = xs"
    and ext_s1_s2: "s1 \<le> s2"
    and counter_s2: "PQueryCounter s2 = PQueryCounter s1"
    by blast
  have a1_eq: "a1 = a" and xs_eq: "xs = rest"
    using tr tr_s1 challenge_props by simp_all
  have assert_props: "a0 = a1 \<and> t = s2"
    using assert unfolding assert_def

    by (cases "a0 = a1") (simp_all add: throw_no_outcome)
  have ext: "s \<le> t"
    using challenge_props ext_s1_s2 assert_props by (meson hash_ext_trans)
  show ?thesis
    using a'_eq a1_eq xs_eq tr_s2 challenge_counter counter_s2
      assert_props ext
    by simp
qed

lemma mmap_replicate_ro_alpha_round_outcome_parse:
  fixes s t :: "'f protocol_channel"
    and alphas rest :: "'f list"
  assumes tr: "PTranscript s = alphas @ rest"
    and alphas_len: "length alphas = n"
    and outcome:
      "Some (alphas', t) \<in>
        set_dist (execute (mmap (replicate n ro_alpha_round)) s)"
  shows
    "alphas' = alphas \<and>
     PTranscript t = rest \<and>
     s \<le> t \<and>
     PQueryCounter t = PQueryCounter s"
  using alphas_len tr outcome
proof (induction n arbitrary: s alphas alphas' t)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems(1) obtain a alphas_tail where
    alphas_eq: "alphas = a # alphas_tail"
    and alphas_tail_len: "length alphas_tail = n"
    by (cases alphas) auto
  from Suc.prems(3) obtain a' s1 alphas'_tail where
    head:
      "Some (a', s1) \<in> set_dist (execute ro_alpha_round s)"
    and tail:
      "Some (alphas'_tail, t) \<in>
        set_dist (execute (mmap (replicate n ro_alpha_round)) s1)"
    and alphas'_eq: "alphas' = a' # alphas'_tail"
    by (auto elim!: set_dist_bindE)
  have tr_head: "PTranscript s = a # (alphas_tail @ rest)"
    using Suc.prems(2) alphas_eq by simp
  have head_props:
    "a' = a \<and>
     PTranscript s1 = alphas_tail @ rest \<and>
     s \<le> s1 \<and>
     PQueryCounter s1 = PQueryCounter s"
    by (rule ro_alpha_round_outcome_parse[OF tr_head head])
  have tail_props:
    "alphas'_tail = alphas_tail \<and>
     PTranscript t = rest \<and>
     s1 \<le> t \<and>
     PQueryCounter t = PQueryCounter s1"
    by (rule Suc.IH[OF alphas_tail_len _ tail])
      (use head_props in simp)
  have ext: "s \<le> t"
    using head_props tail_props by (meson hash_ext_trans)
  show ?case
    using alphas_eq alphas'_eq head_props tail_props ext by simp
qed

lemma ro_verifier_query_round_program_aligns_expected_chunk:
  fixes s t :: "'f protocol_channel"
    and rest chunk :: "'f list"
  assumes chunk_shape:
      "verifier_query_round_chunk expected_idx trace_roots composition_roots
        chunk"
    and tr: "PTranscript s = chunk @ rest"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (ro_verifier_query_round_program fr f_fl f_final as fl final) s)"
  shows
    "PTranscript t = rest \<and>
     ro_absorb_lookup_chain t (PState s) chunk (PState t) \<and>
     s \<le> t \<and>
     PQueryCounter t = Suc (PQueryCounter s)"
proof -
  from ro_verifier_query_round_program_outcome_with_lookup_chain[OF outcome]
  obtain raw s1 parsed_chunk where
    challenge:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and parsed_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        (map snd f_fl) (map snd fl) parsed_chunk"
    and parsed_tr:
      "PTranscript s = parsed_chunk @ PTranscript t"
    and parsed_chain:
      "ro_absorb_lookup_chain t (PState s) parsed_chunk (PState t)"
    and ext: "s \<le> t"
    and counter: "PQueryCounter t = Suc (PQueryCounter s)"
    by blast
  have chunk_len:
    "length chunk =
      verifier_query_round_transcript_length expected_idx
        trace_roots composition_roots"
    by (rule verifier_query_round_chunk_length[OF chunk_shape])
  have parsed_len:
    "length parsed_chunk =
      verifier_query_round_transcript_length (index (to_nat raw))
        (map snd f_fl) (map snd fl)"
    by (rule verifier_query_round_chunk_length[OF parsed_shape])
  have len_eq: "length parsed_chunk = length chunk"
    using chunk_len parsed_len trace_roots_eq composition_roots_eq
    by (simp add: verifier_query_round_transcript_length_index_irrelevant)
  have parsed_take:
    "parsed_chunk = take (length parsed_chunk) (PTranscript s)"
    using parsed_tr by simp
  have chunk_take: "chunk = take (length chunk) (PTranscript s)"
    using tr by simp
  have parsed_eq: "parsed_chunk = chunk"
    using parsed_take chunk_take len_eq by simp
  show ?thesis
    using tr parsed_tr parsed_chain ext counter parsed_eq by simp
qed

lemma ntimes_ro_verifier_query_round_program_aligns_expected_chunks:
  fixes s t :: "'f protocol_channel"
    and chunks :: "'f list list"
    and rest :: "'f list"
  assumes chunks_len: "length chunks = n"
    and expected_len: "length expected_idxs = n"
    and chunk_shapes:
      "\<forall>j < n.
        verifier_query_round_chunk (expected_idxs ! j) trace_roots
          composition_roots (chunks ! j)"
    and tr: "PTranscript s = List.concat chunks @ rest"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program fr f_fl f_final as fl final)
              n)
            s)"
  shows
    "PTranscript t = rest \<and>
     ro_absorb_lookup_chain t (PState s) (List.concat chunks) (PState t) \<and>
     s \<le> t \<and>
     PQueryCounter t = PQueryCounter s + n"
  using chunks_len expected_len chunk_shapes tr outcome
proof (induction n arbitrary: s chunks results t expected_idxs)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  let ?round =
    "ro_verifier_query_round_program fr f_fl f_final as fl final"
  from Suc.prems(1) obtain chunk chunks_tail where
    chunks_eq: "chunks = chunk # chunks_tail"
    and chunks_tail_len: "length chunks_tail = n"
    by (cases chunks) auto
  from Suc.prems(5) obtain result s1 results_tail where
    head: "Some (result, s1) \<in> set_dist (execute ?round s)"
    and tail:
      "Some (results_tail, t) \<in>
        set_dist (execute (ntimes ?round n) s1)"
    and results_eq: "results = result # results_tail"
    by (auto elim!: set_dist_bindE)
  have result_eq: "result = ()"
    by (cases result) simp
  have head_out: "Some ((), s1) \<in> set_dist (execute ?round s)"
    using head result_eq by simp
  have expected_idxs_nonempty: "expected_idxs \<noteq> []"
    using Suc.prems(2) by auto
  then obtain expected_idx expected_idxs_tail where
    expected_idxs_eq: "expected_idxs = expected_idx # expected_idxs_tail"
    by (cases expected_idxs) auto
  have expected_idxs_tail_len: "length expected_idxs_tail = n"
    using Suc.prems(2) expected_idxs_eq by simp
  have head_shape':
    "verifier_query_round_chunk (expected_idxs ! 0) trace_roots
      composition_roots (chunks ! 0)"
    by (rule Suc.prems(3)[rule_format]) simp
  have head_shape:
    "verifier_query_round_chunk expected_idx trace_roots composition_roots
      chunk"
    using head_shape' chunks_eq expected_idxs_eq by simp
  have tail_shapes:
    "\<forall>j < n.
      verifier_query_round_chunk (expected_idxs_tail ! j) trace_roots
        composition_roots (chunks_tail ! j)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < n"
    have
      "verifier_query_round_chunk (expected_idxs ! Suc j) trace_roots
        composition_roots (chunks ! Suc j)"
      by (rule Suc.prems(3)[rule_format]) (use j_bound in simp)
    then show
      "verifier_query_round_chunk (expected_idxs_tail ! j) trace_roots
        composition_roots (chunks_tail ! j)"
      using chunks_eq expected_idxs_eq by simp
  qed
  have tr_head:
    "PTranscript s = chunk @ (List.concat chunks_tail @ rest)"
    using Suc.prems(4) chunks_eq by simp
  have head_props:
    "PTranscript s1 = List.concat chunks_tail @ rest \<and>
     ro_absorb_lookup_chain s1 (PState s) chunk (PState s1) \<and>
     s \<le> s1 \<and>
     PQueryCounter s1 = Suc (PQueryCounter s)"
    by (rule ro_verifier_query_round_program_aligns_expected_chunk[
          OF head_shape tr_head trace_roots_eq composition_roots_eq
            head_out])
  have tail_props:
    "PTranscript t = rest \<and>
     ro_absorb_lookup_chain t (PState s1) (List.concat chunks_tail)
       (PState t) \<and>
     s1 \<le> t \<and>
     PQueryCounter t = PQueryCounter s1 + n"
    by (rule Suc.IH[OF chunks_tail_len expected_idxs_tail_len
          tail_shapes _ tail])
      (use head_props in simp)
  have head_chain_s1:
    "ro_absorb_lookup_chain s1 (PState s) chunk (PState s1)"
    using head_props by simp
  have tail_ext: "s1 \<le> t"
    using tail_props by simp
  have head_chain_final:
    "ro_absorb_lookup_chain t (PState s) chunk (PState s1)"
    by (rule ro_absorb_lookup_chain_mono[OF head_chain_s1 tail_ext])
  have tail_chain:
    "ro_absorb_lookup_chain t (PState s1) (List.concat chunks_tail)
      (PState t)"
    using tail_props by simp
  have chain:
    "ro_absorb_lookup_chain t (PState s)
      (chunk @ List.concat chunks_tail) (PState t)"
    by (rule ro_absorb_lookup_chain_append[
          OF head_chain_final tail_chain])
  have ext: "s \<le> t"
    using head_props tail_props by (meson hash_ext_trans)
  show ?case
    using chunks_eq head_props tail_props chain ext by simp
qed

lemma ro_verify_monad_actual_query_boundaryE:
  fixes sent final_state :: "'f protocol_channel"
  assumes nonempty: "0 < ceil_log clength"
    and trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"

    and composition_len:
      "length (staged_composition_fri_roots data) =
        ceil_log (to_nat (staged_degree data) + 1)"
    and alphas_len: "length (staged_alphas data) = length spec"
    and query_idxs_len: "length query_idxs = rounds"
    and chunks_len: "length (staged_query_chunks data) = rounds"
    and chunk_shapes:
      "\<forall>j < rounds.
        verifier_query_round_chunk (query_idxs ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)"
    and outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary sent
              (staged_proof_transcript data)))"
  obtains f_fl fl verifier_query_state fr f_final as final where
    "fr = staged_trace_root data"
    "map snd f_fl = staged_trace_fri_roots data"
    "map snd fl = staged_composition_fri_roots data"
    "f_fl \<noteq> []"
    "to_nat (staged_degree data) \<le> maxDegree"
    "Some (results, final_state) \<in>
      set_dist
        (execute
          (ntimes
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          verifier_query_state)"
    "PTranscript verifier_query_state =
      List.concat (staged_query_chunks data)"
    "sent \<le> verifier_query_state"
    "PQueryCounter verifier_query_state = 0"
    "ro_absorb_lookup_chain final_state (PState verifier_query_state)
      (List.concat (staged_query_chunks data)) (PState final_state)"
    "verifier_query_state \<le> final_state"
proof -
  let ?start =
    "verifier_state_from_adversary sent (staged_proof_transcript data)"
  from ro_verify_monad_outcomeE[OF outcome]
  obtain fr trace_pairs f_final alphas dg composition_pairs final
      s1 s2 s3 s4 s5 s6 s7 s8 where
    root_out:
      "Some (fr, s1) \<in> set_dist (execute protocol_absorb_read ?start)"
    and trace_out:
      "Some (trace_pairs, s2) \<in>
        set_dist
          (execute (ntimes ro_receive_trace_fri_commits (ceil_log clength))
            s1)"
    and trace_final_out:
      "Some (f_final, s3) \<in>
        set_dist (execute protocol_absorb_read s2)"
    and alpha_out:
      "Some (alphas, s4) \<in>
        set_dist
          (execute (mmap (replicate (length spec) ro_alpha_round)) s3)"
    and degree_out:
      "Some (dg, s5) \<in> set_dist (execute protocol_absorb_read s4)"
    and assert_out:
      "Some ((), s6) \<in>
        set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
    and composition_out:
      "Some (composition_pairs, s7) \<in>
        set_dist
          (execute
            (ntimes ro_receive_composition_fri_commits
              (ceil_log (to_nat dg + 1)))
            s6)"
    and composition_final_out:
      "Some (final, s8) \<in>
        set_dist (execute protocol_absorb_read s7)"
    and query_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program fr trace_pairs f_final alphas
                composition_pairs final)
              rounds)
            s8)"
    by (rule ro_verify_monad_outcomeE[OF outcome])

  have start_tr:
    "PTranscript ?start =
      staged_trace_root data #
        (staged_trace_fri_roots data @
          [staged_trace_final data] @ staged_alphas data @
          [staged_degree data] @ staged_composition_fri_roots data @
          [staged_composition_final data] @
          List.concat (staged_query_chunks data))"
    unfolding staged_proof_transcript_def verifier_header_messages_def
    by simp
  from protocol_absorb_read_outcome_with_lookup_chain[OF root_out]
  obtain root_rest where
    root_value:
      "PTranscript ?start = fr # root_rest"
    and root_tr: "PTranscript s1 = root_rest"
    and root_ext: "?start \<le> s1"
    and root_counter: "PQueryCounter s1 = PQueryCounter ?start"
    by blast
  have fr_eq: "fr = staged_trace_root data"
    and root_rest_eq:
      "root_rest =
        staged_trace_fri_roots data @
          [staged_trace_final data] @ staged_alphas data @
          [staged_degree data] @ staged_composition_fri_roots data @
          [staged_composition_final data] @
          List.concat (staged_query_chunks data)"
    using start_tr root_value by simp_all

  have trace_tr:
    "PTranscript s1 =
      staged_trace_fri_roots data @
        ([staged_trace_final data] @ staged_alphas data @
          [staged_degree data] @ staged_composition_fri_roots data @
          [staged_composition_final data] @
          List.concat (staged_query_chunks data))"
    using root_tr root_rest_eq by simp
  have trace_props:
    "map snd trace_pairs = staged_trace_fri_roots data \<and>
     PTranscript s2 =
       [staged_trace_final data] @ staged_alphas data @
         [staged_degree data] @ staged_composition_fri_roots data @
         [staged_composition_final data] @
         List.concat (staged_query_chunks data) \<and>
     s1 \<le> s2 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    by (rule ntimes_ro_receive_trace_fri_commits_outcome_parse[
          OF trace_tr trace_len trace_out])

  from protocol_absorb_read_outcome_with_lookup_chain[OF trace_final_out]
  obtain trace_final_rest where
    trace_final_value:
      "PTranscript s2 = f_final # trace_final_rest"
    and trace_final_tr: "PTranscript s3 = trace_final_rest"
    and trace_final_ext: "s2 \<le> s3"
    and trace_final_counter: "PQueryCounter s3 = PQueryCounter s2"
    by blast
  have f_final_eq: "f_final = staged_trace_final data"
    and trace_final_rest_eq:
      "trace_final_rest =
        staged_alphas data @ [staged_degree data] @
          staged_composition_fri_roots data @
          [staged_composition_final data] @
          List.concat (staged_query_chunks data)"
    using trace_props trace_final_value by simp_all

  have alpha_tr:
    "PTranscript s3 =
      staged_alphas data @
        ([staged_degree data] @ staged_composition_fri_roots data @
          [staged_composition_final data] @
          List.concat (staged_query_chunks data))"
    using trace_final_tr trace_final_rest_eq by simp
  have alpha_props:
    "alphas = staged_alphas data \<and>
     PTranscript s4 =
       [staged_degree data] @ staged_composition_fri_roots data @
         [staged_composition_final data] @
         List.concat (staged_query_chunks data) \<and>
     s3 \<le> s4 \<and>
     PQueryCounter s4 = PQueryCounter s3"
    by (rule mmap_replicate_ro_alpha_round_outcome_parse[
          OF alpha_tr alphas_len alpha_out])

  from protocol_absorb_read_outcome_with_lookup_chain[OF degree_out]
  obtain degree_rest where
    degree_value: "PTranscript s4 = dg # degree_rest"
    and degree_tr: "PTranscript s5 = degree_rest"
    and degree_ext: "s4 \<le> s5"
    and degree_counter: "PQueryCounter s5 = PQueryCounter s4"
    by blast
  have dg_eq: "dg = staged_degree data"
    and degree_rest_eq:
      "degree_rest =
        staged_composition_fri_roots data @
          [staged_composition_final data] @
          List.concat (staged_query_chunks data)"
    using alpha_props degree_value by simp_all
  have s6_eq: "s6 = s5"
    using assert_out unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (simp_all add: throw_no_outcome)
  have degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    using assert_out dg_eq
    unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (simp_all add: throw_no_outcome)

  have composition_tr:
    "PTranscript s6 =
      staged_composition_fri_roots data @
        ([staged_composition_final data] @
          List.concat (staged_query_chunks data))"
    using degree_tr degree_rest_eq s6_eq by simp
  have composition_props:
    "map snd composition_pairs = staged_composition_fri_roots data \<and>
     PTranscript s7 =
       [staged_composition_final data] @
         List.concat (staged_query_chunks data) \<and>
     s6 \<le> s7 \<and>
     PQueryCounter s7 = PQueryCounter s6"
    by (rule
      ntimes_ro_receive_composition_fri_commits_outcome_parse[
        OF composition_tr _ composition_out])
      (use composition_len dg_eq in simp)

  from protocol_absorb_read_outcome_with_lookup_chain[
      OF composition_final_out]
  obtain final_rest where
    final_value: "PTranscript s7 = final # final_rest"
    and final_tr: "PTranscript s8 = final_rest"
    and final_ext: "s7 \<le> s8"
    and final_counter: "PQueryCounter s8 = PQueryCounter s7"
    by blast
  have final_eq: "final = staged_composition_final data"
    and final_rest_eq:
      "final_rest = List.concat (staged_query_chunks data)"
    using composition_props final_value by simp_all
  have s8_tr:
    "PTranscript s8 = List.concat (staged_query_chunks data)"
    using final_tr final_rest_eq by simp

  have query_props:
    "PTranscript final_state = [] \<and>
     ro_absorb_lookup_chain final_state (PState s8)
       (List.concat (staged_query_chunks data)) (PState final_state) \<and>
     s8 \<le> final_state \<and>
     PQueryCounter final_state = PQueryCounter s8 + rounds"
    by (rule
      ntimes_ro_verifier_query_round_program_aligns_expected_chunks[
        OF chunks_len query_idxs_len chunk_shapes _ _ _ query_out])
      (use s8_tr trace_props composition_props in simp_all)

  have sent_start: "sent \<le> ?start"
    unfolding verifier_state_from_adversary_def less_eq_hash_ext_def
      less_eq_fmap_def
    by simp
  have start_s8: "?start \<le> s8"
    using root_ext trace_props trace_final_ext alpha_props degree_ext
      s6_eq composition_props final_ext
    by (meson hash_ext_trans hash_ext_refl)
  have sent_s8: "sent \<le> s8"
    by (rule hash_ext_trans[OF sent_start start_s8])
  have counter_s8: "PQueryCounter s8 = 0"
    using root_counter trace_props trace_final_counter alpha_props
      degree_counter s6_eq composition_props final_counter
    by simp
  have trace_nonempty: "staged_trace_fri_roots data \<noteq> []"
    using trace_len nonempty by auto
  have pairs_nonempty: "trace_pairs \<noteq> []"
    using trace_props trace_nonempty by auto
  have query_chain:
    "ro_absorb_lookup_chain final_state (PState s8)
      (List.concat (staged_query_chunks data)) (PState final_state)"
    using query_props by blast
  have query_ext: "s8 \<le> final_state"
    using query_props by blast
  show ?thesis
    by (rule that)
      (use fr_eq trace_props composition_props pairs_nonempty degree_bound
        query_out s8_tr sent_s8 counter_s8 query_chain query_ext in simp_all)
qed

end
end
