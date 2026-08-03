(*  Title:      Stark/Soundness_FRI_Query_List_Prequery.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Query_List_Prequery
  imports
    Stark_Core.Merkle_Tree
    Soundness_Core_Events
    Soundness_FRI_Query_Exact_Bounds
    Soundness_FRI_Query_Index_Staged_Bounds
begin

text \<open>
  Query-list prequery accounting for FRI.  The lemmas in this theory relate
  verifier-generated query index lists to random-oracle budget events used in
  the staged soundness proof.
\<close>

context soundness
begin

lemma set_dist_return_valueD:
  assumes "Some (y, t) \<in> set_dist (execute (return x) s)"
  shows "y = x"
  using assms
  unfolding set_dist_def return.rep_eq dist_return_def
  by (simp add: dist_delta_dist delta_map_def)

lemma set_dist_return_stateD:
  assumes "Some (y, t) \<in> set_dist (execute (return x) s)"
  shows "t = s"
  using assms
  unfolding set_dist_def return.rep_eq dist_return_def
  by (simp add: dist_delta_dist delta_map_def)

lemma set_dist_bind_return_consE:
  assumes support:
    "out \<in> set_dist (execute (m \<bind> (\<lambda>xs. return (u # xs))) s)"
    and out_eq: "out = Some (ys, t0)"
  obtains results t where
    "Some (results, t) \<in> set_dist (execute m s)"
    "ys = u # results"
    "t0 = t"
    "out = Some (u # results, t)"
proof -
  from support[unfolded out_eq]
  obtain results t where tail:
      "Some (results, t) \<in> set_dist (execute m s)"
    and ret:
      "Some (ys, t0) \<in> set_dist (execute (return (u # results)) t)"
    by (auto elim!: set_dist_bindE)
  have ys_eq: "ys = u # results"
    by (rule set_dist_return_valueD[OF ret])
  have t0_eq: "t0 = t"
    by (rule set_dist_return_stateD[OF ret])
  have out_eq': "out = Some (u # results, t)"
    using out_eq ys_eq t0_eq by simp
  show ?thesis
    by (rule that[OF tail ys_eq t0_eq out_eq'])
qed

lemma set_dist_bind_return_cons_SomeE:
  assumes support:
    "Some (ys, t) \<in> set_dist (execute (m \<bind> (\<lambda>xs. return (u # xs))) s)"
  obtains xs where
    "Some (xs, t) \<in> set_dist (execute m s)"
    "ys = u # xs"
proof -
  from support obtain xs t0 where tail:
      "Some (xs, t0) \<in> set_dist (execute m s)"
    and ys_eq: "ys = u # xs"
    and t_eq: "t = t0"
    by (elim set_dist_bind_return_consE) simp
  have tail_t: "Some (xs, t) \<in> set_dist (execute m s)"
    by (subst t_eq, rule tail)
  show ?thesis
    by (rule that[OF tail_t ys_eq])
qed

lemma wp_event_nonzero_imp_exists_support:
  assumes "wp_event m P s \<noteq> 0"
  obtains out where "out \<in> set_dist (execute m s)" and "P out"
  by (rule wp_event_pos_imp_exists_support)
    (rule zero_less_iff_neq_zero[THEN iffD2], rule assms)

lemma wp_event_false [simp]:
  "wp_event m (\<lambda>_. False) s = 0"
  unfolding wp_event_def wp_def dist_expect_def
  by simp

lemma wp_event_bind_return_cons_mono:
  fixes m :: "('a list, 's) state_monad"
  assumes none_imp: "Q None \<Longrightarrow> R None"
    and some_imp:
      "\<And>xs t. Some (xs, t) \<in> set_dist (execute m s) \<Longrightarrow>
        Q (Some (u # xs, t)) \<Longrightarrow> R (Some (xs, t))"
  shows
    "wp_event (m \<bind> (\<lambda>xs. return (u # xs))) Q s \<le>
      wp_event m R s"
proof (rule wp_event_bind_bound_by_head_event)
  show "wp_event m R s \<le> wp_event m R s"
    by (rule order.refl)
next
  show "Q None \<Longrightarrow> R None"
    by (rule none_imp)
next
  fix xs t out
  assume support: "Some (xs, t) \<in> set_dist (execute m s)"
    and ret: "out \<in> set_dist (execute (return (u # xs)) t)"
    and q: "Q out"
  have out_eq: "out = Some (u # xs, t)"
    using ret
    unfolding set_dist_def return.rep_eq dist_return_def
      dist_delta_dist delta_map_def
    by simp
  have q_some: "Q (Some (u # xs, t))"
    using q by (simp only: out_eq)
  show "R (Some (xs, t))"
    by (rule some_imp[OF support q_some])
qed

lemma eq_Suc_imp_less_nat:
  assumes "m = Suc n"
  shows "n < m"
  by (subst assms, rule lessI)

lemma list_length_SucE:
  assumes "length xs = Suc n"
  obtains x xs' where "xs = x # xs'"
  using assms by (cases xs) simp_all

lemma state_after_query_chunks_cons_shift:
  assumes "s1 = state_after_query_chunks s (chunk # chunks) 1"
  shows
    "state_after_query_chunks s1 chunks n =
      state_after_query_chunks s (chunk # chunks) (Suc n)"
  using assms unfolding state_after_query_chunks_def by simp

lemma state_after_query_chunks_cons_shift_index:
  assumes "s1 = state_after_query_chunks s (chunk # chunks) 1"
  shows
    "state_after_query_chunks s1 chunks i =
      state_after_query_chunks s (chunk # chunks) (Suc i)"
  using assms unfolding state_after_query_chunks_def by simp

lemma state_after_query_chunks_one_cons:
  "state_after_query_chunks s (chunk # chunks) 1 = foldl concat s chunk"
  unfolding state_after_query_chunks_def by simp

end

text \<open>
  Query-list prequery accounting for sampled FRI.

  The exact verifier-local sampled-query bounds are list-valued: they bound
  the probability of drawing a whole query-index list from a target set.  In
  the staged adversary experiment the verifier reuses the adversary's oracle
  map, so an exact staged theorem needs a fresh/prequeried split for the whole
  query-index list.  This layer provides the conservative relation-budget side
  of that split without changing the oracle model.
\<close>

context soundness
begin

lemma verifier_query_round_program_alt_outcomeE:
  assumes outcome:
    "Some ((), t) \<in>
      set_dist
        (execute
          (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw s0 where
    "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    "Some ((), t) \<in>
      set_dist
        (execute
          (verifier_query_round_after_index_program fr f_fl f_final as fl
            final raw) s0)"
  using outcome[unfolded verifier_query_round_program_alt_def]
  by (auto elim!: set_dist_bindE)

lemma verifier_query_round_parts_counter:
  assumes recv:
      "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    and after:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final raw) s0)"
  shows "PQueryCounter t = Suc (PQueryCounter s)"
proof -
  have counter_s0: "PQueryCounter s0 = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF recv] by simp
  have counter_t_s0: "PQueryCounter t = PQueryCounter s0"
    by (rule conjunct2[OF verifier_query_round_after_index_program_outcome
        [OF after]])
  show ?thesis
  proof (rule HOL.trans)
    show "PQueryCounter t = PQueryCounter s0"
      by (rule counter_t_s0)
    show "PQueryCounter s0 = Suc (PQueryCounter s)"
      by (rule counter_s0)
  qed
qed

definition query_index_raw_list_preimage :: "nat list set \<Rightarrow> 'f list set"
  where
    "query_index_raw_list_preimage Q =
      {raws. length raws = rounds \<and>
        map (\<lambda>raw. index (to_nat raw)) raws \<in> Q}"

definition query_index_raw_list_position_values
  :: "nat list set \<Rightarrow> nat \<Rightarrow> 'f set"
  where
    "query_index_raw_list_position_values Q i =
      {raw. \<exists>raws \<in> query_index_raw_list_preimage Q.
        i < rounds \<and> raw = raws ! i}"

definition query_index_raw_list_relation_fiber_bound
  :: "nat list set \<Rightarrow> nat"
  where
    "query_index_raw_list_relation_fiber_bound Q =
      (\<Sum>i < rounds. card (query_index_raw_list_position_values Q i))"

definition staged_transcript_query_index_list_set_hit
  :: "nat list set \<Rightarrow>
      ('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_transcript_query_index_list_set_hit Q out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (data, attacker_state) \<Rightarrow>
          (\<exists>raw_idxs query_idxs.
            length raw_idxs = rounds \<and>
            query_idxs \<in> Q \<and>
            query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
            (\<forall>i < rounds.
              fmlookup (HashMap attacker_state)
                (QueryIndexChallenge i
                  (state_after_query_chunks
                    (staged_query_start_hash data)
                    (staged_query_chunks data) i)) =
                Some (raw_idxs ! i))))"

definition staged_security_with_data_query_index_list_set_hit
  :: "nat list set \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times>
          unit list) \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_query_index_list_set_hit Q out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, _), result), final_state) \<Rightarrow>
          (\<exists>raw_idxs query_idxs.
            length raw_idxs = rounds \<and>
            query_idxs \<in> Q \<and>
            query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
            (\<forall>i < rounds.
              fmlookup (HashMap final_state)
                (QueryIndexChallenge i
              (state_after_query_chunks
                (staged_query_start_hash data)
                (staged_query_chunks data) i)) =
            Some (raw_idxs ! i))))"

definition staged_security_with_data_state_query_index_list_path_fresh
  :: "nat list set \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times>
          unit list) \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_query_index_list_path_fresh Q out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), result), final_state) \<Rightarrow>
          (\<exists>raw_idxs query_idxs.
            length raw_idxs = rounds \<and>
            query_idxs \<in> Q \<and>
            query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
            (\<forall>i < rounds.
              fmlookup (HashMap final_state)
                (QueryIndexChallenge i
                  (state_after_query_chunks
                    (staged_query_start_hash data)
                    (staged_query_chunks data) i)) =
                Some (raw_idxs ! i) \<and>
              fmlookup
                (HashMap
                  (verifier_state_from_adversary attacker_state
                    (staged_proof_transcript data)))
                (QueryIndexChallenge i
                  (state_after_query_chunks
                    (staged_query_start_hash data)
                    (staged_query_chunks data) i)) =
                None)))"

definition checked_staged_query_index_list_relation
  :: "'f staged_adversary \<Rightarrow> nat list set \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "checked_staged_query_index_list_relation A Q x y \<longleftrightarrow>
      (\<exists>data attacker_state raw_idxs i.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<and>
        raw_idxs \<in> query_index_raw_list_preimage Q \<and>
        i < rounds \<and>
        x = QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i) \<and>
        y = raw_idxs ! i)"

definition staged_security_with_data_state_query_index_list_prequery_hit
  :: "'f staged_adversary \<Rightarrow> nat list set \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times>
          unit list) \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_query_index_list_prequery_hit A Q out
      \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), result), final_state) \<Rightarrow>
          hash_relation_hit
            (checked_staged_query_index_list_relation A Q)
            adversary_initial_state attacker_state)"

definition query_index_list_path_fresh
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> nat \<Rightarrow> 'f list list \<Rightarrow>
      'f list \<Rightarrow> bool"
  where
    "query_index_list_path_fresh s n chunks raws \<longleftrightarrow>
      length raws = n \<and>
      length chunks = n \<and>
      (\<forall>i < n.
        fmlookup (HashMap s)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) chunks i)) = None)"

lemma query_index_list_path_fresh_head_fresh:
  assumes
    "query_index_list_path_fresh s (Suc n) chunks (raw # raws)"
  shows
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
  using assms unfolding query_index_list_path_fresh_def
    state_after_query_chunks_def
  by auto

lemma query_index_list_path_fresh_lookupD:
  assumes fresh: "query_index_list_path_fresh s n chunks raws"
    and i_bound: "i < n"
  shows
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s + i)
        (state_after_query_chunks (PState s) chunks i)) = None"
proof -
  have all:
    "\<forall>j < n.
      fmlookup (HashMap s)
        (QueryIndexChallenge (PQueryCounter s + j)
          (state_after_query_chunks (PState s) chunks j)) = None"
    using fresh unfolding query_index_list_path_fresh_def
    by (elim conjE)
  show ?thesis
    by (rule all[rule_format, OF i_bound])
qed

definition query_rounds_raw_list_path_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_rounds_raw_list_path_hit s raws n out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (results, t) \<Rightarrow>
          (\<exists>chunks.
            length raws = n \<and>
            length chunks = n \<and>
            PState t = state_after_query_chunks (PState s) chunks n \<and>
            query_index_list_path_fresh s n chunks raws \<and>
            (\<forall>i < n.
              fmlookup (HashMap t)
                (QueryIndexChallenge (PQueryCounter s + i)
                (state_after_query_chunks (PState s) chunks i)) =
              Some (raws ! i))))"

lemma query_rounds_raw_list_path_hitI:
  assumes len_raws: "length raws = n"
    and len_chunks: "length chunks = n"
    and state:
      "PState t = state_after_query_chunks (PState s) chunks n"
    and fresh: "query_index_list_path_fresh s n chunks raws"
    and lookup:
      "\<And>i. i < n \<Longrightarrow>
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) chunks i)) =
        Some (raws ! i)"
  shows "query_rounds_raw_list_path_hit s raws n (Some (results, t))"
proof -
  have rhs_eq:
    "query_rounds_raw_list_path_hit s raws n (Some (results, t)) =
      (\<exists>chunks.
        length raws = n \<and>
        length chunks = n \<and>
        PState t = state_after_query_chunks (PState s) chunks n \<and>
        query_index_list_path_fresh s n chunks raws \<and>
        (\<forall>i < n.
          fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s + i)
              (state_after_query_chunks (PState s) chunks i)) =
          Some (raws ! i)))"
    unfolding query_rounds_raw_list_path_hit_def by simp
  show ?thesis
    by (subst rhs_eq, rule exI[of _ chunks],
        intro conjI allI impI,
        rule len_raws, rule len_chunks, rule state,
        rule fresh, rule lookup)
qed

lemma query_rounds_raw_list_path_hit_cons_SomeE:
  assumes
    "query_rounds_raw_list_path_hit s (raw # raws) (Suc n)
      (Some (ys, t))"
  obtains chunks where
    "length raws = n"
    "length chunks = Suc n"
    "PState t = state_after_query_chunks (PState s) chunks (Suc n)"
    "query_index_list_path_fresh s (Suc n) chunks (raw # raws)"
    "\<And>i. i < Suc n \<Longrightarrow>
      fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s + i)
          (state_after_query_chunks (PState s) chunks i)) =
      Some ((raw # raws) ! i)"
proof -
  have hit_eq:
    "query_rounds_raw_list_path_hit s (raw # raws) (Suc n)
      (Some (ys, t)) =
      (\<exists>chunks.
        length (raw # raws) = Suc n \<and>
        length chunks = Suc n \<and>
        PState t = state_after_query_chunks (PState s) chunks (Suc n) \<and>
        query_index_list_path_fresh s (Suc n) chunks (raw # raws) \<and>
        (\<forall>i < Suc n.
          fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s + i)
              (state_after_query_chunks (PState s) chunks i)) =
          Some ((raw # raws) ! i)))"
    unfolding query_rounds_raw_list_path_hit_def by simp
  have ex_chunks:
    "\<exists>chunks.
      length (raw # raws) = Suc n \<and>
      length chunks = Suc n \<and>
      PState t = state_after_query_chunks (PState s) chunks (Suc n) \<and>
      query_index_list_path_fresh s (Suc n) chunks (raw # raws) \<and>
      (\<forall>i < Suc n.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) chunks i)) =
        Some ((raw # raws) ! i))"
    using assms by (simp only: hit_eq)
  then obtain chunks where len_raws_full: "length (raw # raws) = Suc n"
    and len_chunks: "length chunks = Suc n"
    and state: "PState t = state_after_query_chunks (PState s) chunks (Suc n)"
    and fresh: "query_index_list_path_fresh s (Suc n) chunks (raw # raws)"
    and lookup_all:
      "\<forall>i < Suc n.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) chunks i)) =
        Some ((raw # raws) ! i)"
    by blast
  have len_raws: "length raws = n"
    using len_raws_full by simp
  have lookup:
    "\<And>i. i < Suc n \<Longrightarrow>
      fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s + i)
          (state_after_query_chunks (PState s) chunks i)) =
      Some ((raw # raws) ! i)"
    using lookup_all by blast
  show ?thesis
    by (rule that[OF len_raws len_chunks state fresh lookup])
qed

definition query_round_any_raw_set_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f set \<Rightarrow>
      (unit \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_round_any_raw_set_hit s B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (_, t) \<Rightarrow>
          (\<exists>raw \<in> B.
            fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s) (PState s)) =
          Some raw))"

lemma query_round_any_raw_set_hit_None:
  "\<not> query_round_any_raw_set_hit s B None"
  unfolding query_round_any_raw_set_hit_def by simp

lemma query_round_any_raw_set_hit_NoneE:
  assumes "query_round_any_raw_set_hit s B None"
  shows P
  using assms query_round_any_raw_set_hit_None by contradiction

lemma query_round_any_raw_set_hitI:
  assumes "raw \<in> B"
    and "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
  shows "query_round_any_raw_set_hit s B (Some (u, t))"
proof -
  have hit_eq:
    "query_round_any_raw_set_hit s B (Some (u, t)) =
      (\<exists>raw \<in> B.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw)"
    unfolding query_round_any_raw_set_hit_def by simp
  show ?thesis
    by (subst hit_eq, rule bexI[of _ raw], rule assms(2), rule assms(1))
qed

lemma query_round_any_raw_set_hit_SomeE:
  assumes "query_round_any_raw_set_hit s B (Some (u, t))"
  obtains raw where
    "raw \<in> B"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  have hit_eq:
    "query_round_any_raw_set_hit s B (Some (u, t)) =
      (\<exists>raw \<in> B.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw)"
    unfolding query_round_any_raw_set_hit_def by simp
  have "\<exists>raw \<in> B.
      fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using assms by (simp only: hit_eq)
  then show ?thesis
    by (blast intro: that)
qed

lemma receive_query_index_challenge_current_lookupD:
  assumes "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
  shows
    "fmlookup (HashMap s0)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  have recv_info:
    "s \<le> s0 \<and>
     PState s0 = PState s \<and>
     PTranscript s0 = PTranscript s \<and>
     fmlookup (HashMap s0)
       (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule receive_query_index_challenge_outcome[OF assms])
  show ?thesis
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF recv_info]]])
qed

lemma verifier_query_round_after_index_program_preserves_current_lookupD:
  assumes after:
      "Some (u, t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final raw) s0)"
    and lookup:
      "fmlookup (HashMap s0)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
  shows
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  let ?key = "QueryIndexChallenge (PQueryCounter s) (PState s)"
  have u_eq: "u = ()"
    by (cases u) simp
  have preserve:
    "fmlookup (HashMap t) ?key = fmlookup (HashMap s0) ?key"
    by (rule verifier_query_round_after_index_program_preserves_query_lookup
        [OF after[unfolded u_eq]])
  show ?thesis
  proof (rule HOL.trans)
    show "fmlookup (HashMap t) ?key = fmlookup (HashMap s0) ?key"
      by (rule preserve)
    show "fmlookup (HashMap s0) ?key = Some raw"
      by (rule lookup)
  qed
qed

lemma wp_receive_query_index_challenge_raw_set_le:
  assumes fresh:
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
  shows
    "wp_event receive_query_index_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (raw, _) \<Rightarrow> raw \<in> B)
      s \<le> nnreal (card B) / nnreal size"
proof -
  have eq:
    "wp_event receive_query_index_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (raw, _) \<Rightarrow> raw \<in> B)
      s = nnreal (card B) / nnreal size"
    by (rule wp_receive_query_index_challenge_fresh_set[OF fresh])
  show ?thesis
    by (subst eq, rule order_refl)
qed

lemma finite_query_index_raw_list_preimage[simp]:
  "finite (query_index_raw_list_preimage Q)"
proof -
  have "query_index_raw_list_preimage Q \<subseteq> {xs. length xs = rounds}"
    unfolding query_index_raw_list_preimage_def by auto
  then show ?thesis
    apply (rule finite_subset) by (simp add: finite_list_length)
qed

lemma finite_query_index_raw_list_position_values[simp]:
  "finite (query_index_raw_list_position_values Q i)"
proof -
  have "query_index_raw_list_position_values Q i \<subseteq> UNIV"
    by simp
  then show ?thesis
    by (rule finite_subset) simp
qed

lemma query_index_list_path_fresh_tail_lookup:
  assumes fresh:
    "query_index_list_path_fresh s (Suc n) (chunk # chunks) (raw # raws)"
    and head:
      "Some ((), s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and head_chunk:
      "PState s1 = foldl concat (PState s) chunk"
    and head_counter:
      "PQueryCounter s1 = Suc (PQueryCounter s)"
    and i_bound: "i < n"
  shows
    "fmlookup (HashMap s1)
      (QueryIndexChallenge (PQueryCounter s1 + i)
        (state_after_query_chunks (PState s1) chunks i)) = None"
proof -
  from verifier_query_round_program_alt_outcomeE[OF head]
  obtain raw_idx s0 where recv:
      "Some (raw_idx, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    and after:
      "Some ((), s1) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final raw_idx) s0)"
    by blast
  let ?tail_key =
    "QueryIndexChallenge (PQueryCounter s1 + i)
      (state_after_query_chunks (PState s1) chunks i)"
  let ?full_key =
    "QueryIndexChallenge (PQueryCounter s + Suc i)
      (state_after_query_chunks (PState s) (chunk # chunks) (Suc i))"
  have key_eq: "?tail_key = ?full_key"
    using head_chunk head_counter
    unfolding state_after_query_chunks_def
    by simp
  have suc_i_bound: "Suc i < Suc n"
    using i_bound by simp
  have full_none:
    "fmlookup (HashMap s) ?full_key = None"
    by (rule query_index_list_path_fresh_lookupD[OF fresh suc_i_bound])
  have neq:
    "?full_key \<noteq> QueryIndexChallenge (PQueryCounter s) (PState s)"
    by simp
  have lookup_s0:
    "fmlookup (HashMap s0) ?full_key = None"
  proof -
    have preserve:
      "fmlookup (HashMap s0) ?full_key =
        fmlookup (HashMap s) ?full_key"
      by (rule receive_query_index_challenge_preserves_other_lookup
          [OF recv neq])
    show ?thesis
    proof (rule HOL.trans)
      show "fmlookup (HashMap s0) ?full_key =
        fmlookup (HashMap s) ?full_key"
        by (rule preserve)
      show "fmlookup (HashMap s) ?full_key = None"
        by (rule full_none)
    qed
  qed
  have lookup_s1:
    "fmlookup (HashMap s1) ?full_key = None"
  proof -
    have preserve:
      "fmlookup (HashMap s1) ?full_key =
        fmlookup (HashMap s0) ?full_key"
      by (rule verifier_query_round_after_index_program_preserves_query_lookup
          [OF after])
    show ?thesis
    proof (rule HOL.trans)
      show "fmlookup (HashMap s1) ?full_key =
        fmlookup (HashMap s0) ?full_key"
        by (rule preserve)
      show "fmlookup (HashMap s0) ?full_key = None"
        by (rule lookup_s0)
    qed
  qed
  show ?thesis
    unfolding key_eq by (rule lookup_s1)
qed

lemma query_index_list_path_fresh_tail:
  assumes fresh:
    "query_index_list_path_fresh s (Suc n) (chunk # chunks) (raw # raws)"
    and head:
      "Some ((), s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and head_chunk:
      "PState s1 = foldl concat (PState s) chunk"
    and head_counter:
      "PQueryCounter s1 = Suc (PQueryCounter s)"
  shows "query_index_list_path_fresh s1 n chunks raws"
proof -
  have len_raws: "length raws = n"
    using fresh unfolding query_index_list_path_fresh_def by simp
  have len_chunks: "length chunks = n"
    using fresh unfolding query_index_list_path_fresh_def by simp
  have lookup_none:
    "\<And>i. i < n \<Longrightarrow>
      fmlookup (HashMap s1)
        (QueryIndexChallenge (PQueryCounter s1 + i)
          (state_after_query_chunks (PState s1) chunks i)) = None"
    by (rule query_index_list_path_fresh_tail_lookup
        [OF fresh head head_chunk head_counter])
  show ?thesis
    unfolding query_index_list_path_fresh_def
    using len_raws len_chunks lookup_none by simp
qed

lemma query_rounds_first_tail_key_fresh_after_head:
  assumes fresh:
      "query_index_list_path_fresh s (Suc n) chunks (raw # raws)"
    and head:
      "Some ((), s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and one_bound: "1 < Suc n"
    and head_counter: "PQueryCounter s1 = Suc (PQueryCounter s)"
  shows
    "fmlookup (HashMap s1)
      (QueryIndexChallenge (PQueryCounter s1)
        (state_after_query_chunks (PState s) chunks 1)) = None"
proof -
  let ?y = "state_after_query_chunks (PState s) chunks 1"
  let ?full_key = "QueryIndexChallenge (PQueryCounter s + 1) ?y"
  have full_none_s: "fmlookup (HashMap s) ?full_key = None"
    by (rule query_index_list_path_fresh_lookupD[OF fresh one_bound])
  from verifier_query_round_program_alt_outcomeE[OF head]
  obtain r s0 where recv:
      "Some (r, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    and after:
      "Some ((), s1) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final r) s0)"
    by blast
  have neq:
    "?full_key \<noteq> QueryIndexChallenge (PQueryCounter s) (PState s)"
    by simp
  have s0_none:
    "fmlookup (HashMap s0) ?full_key = None"
  proof -
    have preserve:
      "fmlookup (HashMap s0) ?full_key =
        fmlookup (HashMap s) ?full_key"
      by (rule receive_query_index_challenge_preserves_other_lookup
          [OF recv neq])
    show ?thesis
    proof (rule HOL.trans)
      show "fmlookup (HashMap s0) ?full_key =
        fmlookup (HashMap s) ?full_key"
        by (rule preserve)
      show "fmlookup (HashMap s) ?full_key = None"
        by (rule full_none_s)
    qed
  qed
  have s1_none: "fmlookup (HashMap s1) ?full_key = None"
  proof -
    have preserve:
      "fmlookup (HashMap s1) ?full_key =
        fmlookup (HashMap s0) ?full_key"
      by (rule verifier_query_round_after_index_program_preserves_query_lookup
          [OF after])
    show ?thesis
    proof (rule HOL.trans)
      show "fmlookup (HashMap s1) ?full_key =
        fmlookup (HashMap s0) ?full_key"
        by (rule preserve)
      show "fmlookup (HashMap s0) ?full_key = None"
        by (rule s0_none)
    qed
  qed
  show ?thesis
    using head_counter s1_none by simp
qed

lemma query_rounds_raw_list_path_hit_tail_head_state:
  assumes head:
      "Some ((), s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and tail:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s1)"
    and len_chunks_suc: "length chunks = Suc n"
    and state_t:
      "PState t = state_after_query_chunks (PState s) chunks (Suc n)"
    and fresh:
      "query_index_list_path_fresh s (Suc n) chunks (raw # raws)"
    and lookups:
      "\<And>i. i < Suc n \<Longrightarrow>
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) chunks i)) =
        Some ((raw # raws) ! i)"
    and chunks_eq: "chunks = chunk # chunks_tail"
    and head_counter: "PQueryCounter s1 = Suc (PQueryCounter s)"
  shows "PState s1 = state_after_query_chunks (PState s) chunks 1"
proof (cases n)
  case 0
  then have "results = []" "t = s1"
    using tail by simp_all
  then show ?thesis
    using state_t 0 unfolding chunks_eq state_after_query_chunks_def by simp
next
  case (Suc m)
  from tail[unfolded Suc ntimes.simps] obtain u' s2 rest t0 where tail_head:
      "Some (u', s2) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s1)"
    and tail_rest0:
      "Some (rest, t0) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) m)
            s2)"
    and ret:
      "Some (results, t) \<in> set_dist (execute (return (u' # rest)) t0)"
    by (auto elim!: set_dist_bindE)
  have results_eq: "results = u' # rest"
    by (rule set_dist_return_valueD[OF ret])
  have t_eq: "t = t0"
    by (rule set_dist_return_stateD[OF ret])
  have tail_rest:
    "Some (rest, t) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final) m)
          s2)"
    by (subst t_eq, rule tail_rest0)
	  have u'_eq: "u' = ()"
	    by (cases u') simp
	  let ?y = "state_after_query_chunks (PState s) chunks 1"
	  let ?key = "QueryIndexChallenge (PQueryCounter s1) ?y"
	  have full_none_s1:
	    "fmlookup (HashMap s1) ?key = None"
	    by (rule query_rounds_first_tail_key_fresh_after_head
	        [OF fresh head _ head_counter])
	      (use Suc in simp)
  have lookup_t:
    "fmlookup (HashMap t) ?key = Some (raws ! 0)"
    using lookups[of 1] Suc head_counter
    unfolding chunks_eq state_after_query_chunks_def by simp
  have key_eq:
    "?key = QueryIndexChallenge (PQueryCounter s1) (PState s1)"
  proof (rule ccontr)
    assume neq:
      "?key \<noteq> QueryIndexChallenge (PQueryCounter s1) (PState s1)"
    have tail_head_unit:
      "Some ((), s2) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s1)"
      using tail_head u'_eq by simp
    from verifier_query_round_program_alt_outcomeE[OF tail_head_unit]
    obtain r s0 where recv:
        "Some (r, s0) \<in> set_dist (execute receive_query_index_challenge s1)"
      and after:
        "Some ((), s2) \<in>
          set_dist
            (execute
              (verifier_query_round_after_index_program fr f_fl f_final as fl
                final r) s0)"
      by blast
    have s0_none:
      "fmlookup (HashMap s0) ?key = None"
      using receive_query_index_challenge_preserves_other_lookup[OF recv neq]
        full_none_s1
      by simp
    have s2_none: "fmlookup (HashMap s2) ?key = None"
    proof -
      have preserve:
        "fmlookup (HashMap s2) ?key = fmlookup (HashMap s0) ?key"
        by (rule verifier_query_round_after_index_program_preserves_query_lookup
            [OF after])
      show ?thesis
      proof (rule HOL.trans)
        show "fmlookup (HashMap s2) ?key = fmlookup (HashMap s0) ?key"
          by (rule preserve)
        show "fmlookup (HashMap s0) ?key = None"
          by (rule s0_none)
      qed
    qed
    from verifier_query_round_program_outcome[OF tail_head[unfolded u'_eq]]
    obtain r2::'f and idx2::nat and chunk2::"'f list" where
      counter_s2: "PQueryCounter s2 = Suc (PQueryCounter s1)"
      by blast
    have lookup_pres:
      "fmlookup (HashMap t) ?key = fmlookup (HashMap s2) ?key"
      by (rule ntimes_verifier_query_round_program_preserves_past_query_lookup
          [OF _ tail_rest])
        (use counter_s2 in simp)
    show False
      using lookup_t s2_none lookup_pres by simp
  qed
  then show ?thesis
    by simp
qed

end

context soundness
begin

lemma query_rounds_raw_list_path_hit_tail:
  assumes head:
      "Some ((), s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and tail:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s1)"
    and hit:
      "query_rounds_raw_list_path_hit s (raw # raws) (Suc n)
        (Some (u # results, t))"
  shows "query_rounds_raw_list_path_hit s1 raws n (Some (results, t))"
proof -
  from query_rounds_raw_list_path_hit_cons_SomeE[OF hit] obtain chunks where
    len_raws: "length raws = n"
    and len_chunks_suc: "length chunks = Suc n"
    and state_t:
      "PState t = state_after_query_chunks (PState s) chunks (Suc n)"
    and fresh:
      "query_index_list_path_fresh s (Suc n) chunks (raw # raws)"
    and lookups:
      "\<And>i. i < Suc n \<Longrightarrow>
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) chunks i)) =
        Some ((raw # raws) ! i)"
    by blast
  obtain chunk chunks_tail where chunks_eq: "chunks = chunk # chunks_tail"
    using len_chunks_suc by (cases chunks) auto
  have len_chunks_tail: "length chunks_tail = n"
    using len_chunks_suc unfolding chunks_eq by simp
  from verifier_query_round_program_outcome[OF head]
  obtain raw0::'f and idx::nat and chunk0:: "'f list" where
    head_counter: "PQueryCounter s1 = Suc (PQueryCounter s)"
    by blast
  have head_state:
    "PState s1 = state_after_query_chunks (PState s) chunks 1"
    by (rule query_rounds_raw_list_path_hit_tail_head_state
        [OF head tail len_chunks_suc state_t fresh lookups chunks_eq
          head_counter])
  have fresh_tail:
    "query_index_list_path_fresh s1 n chunks_tail raws"
  proof -
    have fresh_chunks:
      "query_index_list_path_fresh s (Suc n) (chunk # chunks_tail)
        (raw # raws)"
      by (subst chunks_eq[symmetric], rule fresh)
    have head_chunk: "PState s1 = foldl concat (PState s) chunk"
    proof -
      have head_state_cons:
        "PState s1 =
          state_after_query_chunks (PState s) (chunk # chunks_tail) 1"
        by (subst chunks_eq[symmetric], rule head_state)
      show ?thesis
        by (subst state_after_query_chunks_one_cons[symmetric],
            rule head_state_cons)
    qed
    show ?thesis
      by (rule query_index_list_path_fresh_tail
          [OF fresh_chunks head head_chunk head_counter])
  qed
  have state_tail:
    "PState t =
      state_after_query_chunks (PState s1) chunks_tail n"
  proof -
    have shift:
      "state_after_query_chunks (PState s1) chunks_tail n =
        state_after_query_chunks (PState s) (chunk # chunks_tail) (Suc n)"
      by (rule state_after_query_chunks_cons_shift)
        (use head_state chunks_eq in simp)
    show ?thesis
      by (subst shift, subst chunks_eq[symmetric], rule state_t)
  qed
  have lookup_tail:
    "\<And>i. i < n \<Longrightarrow>
      fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s1 + i)
          (state_after_query_chunks (PState s1) chunks_tail i)) =
      Some (raws ! i)"
  proof -
    fix i
    assume i_bound: "i < n"
    have key_eq:
      "QueryIndexChallenge (PQueryCounter s1 + i)
          (state_after_query_chunks (PState s1) chunks_tail i) =
       QueryIndexChallenge (PQueryCounter s + Suc i)
          (state_after_query_chunks (PState s) chunks (Suc i))"
    proof -
      have st_shift:
        "state_after_query_chunks (PState s1) chunks_tail i =
          state_after_query_chunks (PState s) (chunk # chunks_tail) (Suc i)"
        by (rule state_after_query_chunks_cons_shift_index)
          (use head_state chunks_eq in simp)
      show ?thesis
        using head_counter st_shift unfolding chunks_eq by simp
    qed
    show "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s1 + i)
          (state_after_query_chunks (PState s1) chunks_tail i)) =
      Some (raws ! i)"
      using lookups[of "Suc i"] i_bound key_eq by simp
  qed
  show ?thesis
    by (rule query_rounds_raw_list_path_hitI
        [OF len_raws len_chunks_tail state_tail fresh_tail lookup_tail])
qed

end

context soundness
begin

lemma query_rounds_raw_list_path_hit_head:
  assumes head:
      "Some ((), s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and tail:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s1)"
    and hit:
      "query_rounds_raw_list_path_hit s (raw # raws) (Suc n)
        (Some (u # results, t))"
  shows "query_round_any_raw_set_hit s {raw} (Some ((), s1))"
proof -
  have lookup_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
  proof -
    from query_rounds_raw_list_path_hit_cons_SomeE[OF hit]
    obtain chunks where lookup:
      "\<And>i. i < Suc n \<Longrightarrow>
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) chunks i)) =
        Some ((raw # raws) ! i)"
      by blast
    have lookup0:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s + 0)
          (state_after_query_chunks (PState s) chunks 0)) =
        Some ((raw # raws) ! 0)"
      using lookup[of 0] by simp
    show ?thesis
      using lookup0 unfolding state_after_query_chunks_def by simp
  qed
  from verifier_query_round_program_alt_outcomeE[OF head]
  obtain raw0 s0 where
    recv:
      "Some (raw0, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    and after:
      "Some ((), s1) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final raw0) s0)"
    by blast
  have counter_s1: "PQueryCounter s1 = Suc (PQueryCounter s)"
    by (rule verifier_query_round_parts_counter[OF recv after])
  have past: "PQueryCounter s < PQueryCounter s1"
    by (rule eq_Suc_imp_less_nat[OF counter_s1])
  have lookup_s1:
    "fmlookup (HashMap s1)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
  proof -
    let ?key = "QueryIndexChallenge (PQueryCounter s) (PState s)"
    have preserve:
      "fmlookup (HashMap t) ?key = fmlookup (HashMap s1) ?key"
      by (rule ntimes_verifier_query_round_program_preserves_past_query_lookup
          [OF past tail])
    show ?thesis
    proof (rule HOL.trans)
      show "fmlookup (HashMap s1) ?key = fmlookup (HashMap t) ?key"
        by (rule HOL.sym[OF preserve])
      show "fmlookup (HashMap t) ?key = Some raw"
        by (rule lookup_t)
    qed
  qed
  show ?thesis
    by (rule query_round_any_raw_set_hitI[OF singletonI lookup_s1])
qed

lemma verifier_query_round_program_raw_set_hit_imp_raw_in_Some:
  assumes recv:
      "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    and after:
      "Some (u, t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final raw) s0)"
    and hit: "query_round_any_raw_set_hit s B (Some (u, t))"
  shows "raw \<in> B"
proof -
  from query_round_any_raw_set_hit_SomeE[OF hit]
  obtain raw' where
    raw'_in: "raw' \<in> B"
    and lookup_t:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw'"
    by blast
  have lookup_s0:
    "fmlookup (HashMap s0)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule receive_query_index_challenge_current_lookupD[OF recv])
  have lookup_t_current:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule verifier_query_round_after_index_program_preserves_current_lookupD
        [OF after lookup_s0])
  have some_eq: "Some raw = Some raw'"
    using lookup_t_current lookup_t by simp
  have raw_eq: "raw = raw'"
    using some_eq by simp
  show ?thesis
    by (subst raw_eq, rule raw'_in)
qed

lemma verifier_query_round_program_raw_set_hit_imp_raw_in:
  assumes recv:
      "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    and after:
      "out \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final raw) s0)"
    and hit: "query_round_any_raw_set_hit s B out"
  shows "raw \<in> B"
proof -
  have rhs:
    "(case out of
      None \<Rightarrow> False
    | Some (_, t) \<Rightarrow>
        (\<exists>raw' \<in> B.
          fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s) (PState s)) =
          Some raw'))"
    using hit by (simp only: query_round_any_raw_set_hit_def)
  obtain u t where out_eq: "out = Some (u, t)"
  proof (cases out)
    case None
    have False
      using rhs None by simp
    then show ?thesis
      by (rule FalseE)
  next
    case (Some pair)
    then obtain a b where "out = Some (a, b)"
      by (cases pair) auto
    then show ?thesis
      by (rule that)
  qed
  have after_some:
    "Some (u, t) \<in>
      set_dist
        (execute
          (verifier_query_round_after_index_program fr f_fl f_final as fl
            final raw) s0)"
    by (subst out_eq[symmetric]) (rule after)
  have hit_some: "query_round_any_raw_set_hit s B (Some (u, t))"
    by (subst out_eq[symmetric]) (rule hit)
  show ?thesis
    by (rule verifier_query_round_program_raw_set_hit_imp_raw_in_Some
        [OF recv after_some hit_some])
qed

lemma wp_verifier_query_round_program_any_raw_set_bound:
  assumes fresh:
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
  shows
    "wp_event (verifier_query_round_program fr f_fl f_final as fl final)
      (query_round_any_raw_set_hit s B) s \<le>
      nnreal (card B) / nnreal size"
  unfolding verifier_query_round_program_alt_def
proof (rule wp_event_bind_bound_by_head_event)
  show "wp_event receive_query_index_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (raw, _) \<Rightarrow> raw \<in> B)
      s \<le> nnreal (card B) / nnreal size"
    by (rule wp_receive_query_index_challenge_raw_set_le[OF fresh])
next
  show "query_round_any_raw_set_hit s B None \<Longrightarrow>
    (case None of None \<Rightarrow> False | Some (raw, _) \<Rightarrow> raw \<in> B)"
    by (rule query_round_any_raw_set_hit_NoneE)
next
  fix raw s0 out
  assume recv:
    "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    and out:
      "out \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final raw) s0)"
    and hit: "query_round_any_raw_set_hit s B out"
  show "(case Some (raw, s0) of None \<Rightarrow> False | Some (raw, _) \<Rightarrow> raw \<in> B)"
  proof -
    have raw_in: "raw \<in> B"
      by (rule verifier_query_round_program_raw_set_hit_imp_raw_in
          [where s=s and B=B and raw=raw and s0=s0 and out=out
            and fr=fr and f_fl=f_fl and f_final=f_final and as=as
            and fl=fl and final=final, OF recv out hit])
    then show ?thesis
      by simp
  qed
qed

lemma query_rounds_raw_list_path_hit_SomeE:
  assumes "query_rounds_raw_list_path_hit s raws n out"
  obtains results t where "out = Some (results, t)"
proof -
  show ?thesis
  proof (cases out)
    case None
    have none_eq: "query_rounds_raw_list_path_hit s raws n None = False"
      unfolding query_rounds_raw_list_path_hit_def by simp
    have hit_none: "query_rounds_raw_list_path_hit s raws n None"
      by (subst None[symmetric], rule assms)
    then show ?thesis
      using hit_none by (simp only: none_eq)
  next
    case (Some pair)
    then obtain results t where "out = Some (results, t)"
      by (cases pair) auto
    then show ?thesis
      by (rule that)
  qed
qed

lemma query_rounds_raw_list_path_hit_some_fresh_currentD:
  assumes hit:
    "query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n)
      (Some (ys, t))"
  shows
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
proof -
  have some_eq:
    "query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n)
      (Some (ys, t)) =
      (\<exists>chunks.
        length (raw # raws_tail) = Suc n \<and>
        length chunks = Suc n \<and>
        PState t = state_after_query_chunks (PState s) chunks (Suc n) \<and>
        query_index_list_path_fresh s (Suc n) chunks (raw # raws_tail) \<and>
        (\<forall>i < Suc n.
          fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s + i)
              (state_after_query_chunks (PState s) chunks i)) =
          Some ((raw # raws_tail) ! i)))"
    unfolding query_rounds_raw_list_path_hit_def by simp
  have ex_chunks:
    "\<exists>chunks.
      length (raw # raws_tail) = Suc n \<and>
      length chunks = Suc n \<and>
      PState t = state_after_query_chunks (PState s) chunks (Suc n) \<and>
      query_index_list_path_fresh s (Suc n) chunks (raw # raws_tail) \<and>
      (\<forall>i < Suc n.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) chunks i)) =
        Some ((raw # raws_tail) ! i))"
    using hit by (simp only: some_eq)
  then obtain chunks where fresh_path:
    "query_index_list_path_fresh s (Suc n) chunks (raw # raws_tail)"
    by (elim exE conjE)
  show ?thesis
    by (rule query_index_list_path_fresh_head_fresh[OF fresh_path])
qed

lemma query_rounds_raw_list_path_hit_some_head_lookupD:
  assumes hit:
    "query_rounds_raw_list_path_hit s (raw # raws) (Suc n)
      (Some (ys, t))"
  shows
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  have some_eq:
    "query_rounds_raw_list_path_hit s (raw # raws) (Suc n)
      (Some (ys, t)) =
      (\<exists>chunks.
        length (raw # raws) = Suc n \<and>
        length chunks = Suc n \<and>
        PState t = state_after_query_chunks (PState s) chunks (Suc n) \<and>
        query_index_list_path_fresh s (Suc n) chunks (raw # raws) \<and>
        (\<forall>i < Suc n.
          fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s + i)
              (state_after_query_chunks (PState s) chunks i)) =
          Some ((raw # raws) ! i)))"
    unfolding query_rounds_raw_list_path_hit_def by simp
  have ex_chunks:
    "\<exists>chunks.
      length (raw # raws) = Suc n \<and>
      length chunks = Suc n \<and>
      PState t = state_after_query_chunks (PState s) chunks (Suc n) \<and>
      query_index_list_path_fresh s (Suc n) chunks (raw # raws) \<and>
      (\<forall>i < Suc n.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) chunks i)) =
        Some ((raw # raws) ! i))"
    using hit by (simp only: some_eq)
  then obtain chunks where lookup_all:
    "\<forall>i < Suc n.
      fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s + i)
          (state_after_query_chunks (PState s) chunks i)) =
      Some ((raw # raws) ! i)"
    by (elim exE conjE)
  have lookup0:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s + 0)
        (state_after_query_chunks (PState s) chunks 0)) =
      Some ((raw # raws) ! 0)"
  proof -
    have "0 < Suc n"
      by simp
    from lookup_all this show ?thesis
      by blast
  qed
  show ?thesis
    using lookup0 unfolding state_after_query_chunks_def by simp
qed

lemma query_rounds_raw_list_path_hit_bind_headD:
  assumes head:
      "Some (u, s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and support:
      "out \<in>
        set_dist
          (execute
            (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n
              \<bind> (\<lambda>xs. return (u # xs))) s1)"
    and hit:
      "query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n) out"
  shows "query_round_any_raw_set_hit s {raw} (Some (u, s1))"
proof -
  let ?tail =
    "ntimes (verifier_query_round_program fr f_fl f_final as fl final) n"
  from hit obtain ys t0 where out_some: "out = Some (ys, t0)"
    by (rule query_rounds_raw_list_path_hit_SomeE)
  from support out_some obtain results t where tail:
      "Some (results, t) \<in> set_dist (execute ?tail s1)"
    and out_eq: "out = Some (u # results, t)"
    by (elim set_dist_bind_return_consE)
  have u_eq: "u = ()"
    by (cases u) simp
  have head_unit:
    "Some ((), s1) \<in>
      set_dist
        (execute
          (verifier_query_round_program fr f_fl f_final as fl final) s)"
    using head u_eq by simp
  have hit_head_out:
    "query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n)
      (Some (u # results, t))"
    by (subst out_eq[symmetric], rule hit)
  have "query_round_any_raw_set_hit s {raw} (Some ((), s1))"
    by (rule query_rounds_raw_list_path_hit_head
        [OF head_unit tail hit_head_out])
  then show ?thesis
    using u_eq by simp
qed

lemma query_rounds_raw_list_path_hit_cont_zero_if_not_head:
  assumes head:
      "Some (u, s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and not_head:
      "\<not> (fmlookup (HashMap s)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = None \<and>
        query_round_any_raw_set_hit s {raw} (Some (u, s1)))"
  shows
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n
        \<bind> (\<lambda>xs. return (u # xs)))
      (query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n))
      s1 = 0"
proof (rule ccontr)
  let ?tail =
    "ntimes (verifier_query_round_program fr f_fl f_final as fl final) n"
  assume nonzero:
    "wp_event (?tail \<bind> (\<lambda>xs. return (u # xs)))
      (query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n))
      s1 \<noteq> 0"
  from wp_event_nonzero_imp_exists_support[OF nonzero]
  obtain out where out_support:
      "out \<in> set_dist (execute (?tail \<bind> (\<lambda>xs. return (u # xs))) s1)"
    and hit:
      "query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n) out"
    by blast
  from hit obtain ys t0 where out_some: "out = Some (ys, t0)"
    by (rule query_rounds_raw_list_path_hit_SomeE)
  have hit_some:
    "query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n)
      (Some (ys, t0))"
    by (subst out_some[symmetric], rule hit)
  have fresh_current:
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
    by (rule query_rounds_raw_list_path_hit_some_fresh_currentD[OF hit_some])
  have raw_head:
    "query_round_any_raw_set_hit s {raw} (Some (u, s1))"
    by (rule query_rounds_raw_list_path_hit_bind_headD[OF head out_support hit])
  show False
    using not_head fresh_current raw_head by blast
qed

lemma query_rounds_raw_list_path_hit_cont_le_tail:
  assumes head:
      "Some (u, s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  shows
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n
        \<bind> (\<lambda>xs. return (u # xs)))
      (query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n))
      s1
    \<le> wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n)
      (query_rounds_raw_list_path_hit s1 raws_tail n) s1"
proof -
  let ?tail =
    "ntimes (verifier_query_round_program fr f_fl f_final as fl final) n"
  have u_eq: "u = ()"
    by (cases u) simp
  show ?thesis
  proof (rule wp_event_bind_bound_by_head_event)
    show "wp_event ?tail
        (query_rounds_raw_list_path_hit s1 raws_tail n) s1
      \<le> wp_event ?tail
        (query_rounds_raw_list_path_hit s1 raws_tail n) s1"
      by simp
  next
    show
      "query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n) None
        \<Longrightarrow> query_rounds_raw_list_path_hit s1 raws_tail n None"
      unfolding query_rounds_raw_list_path_hit_def by simp
  next
    fix results t out
    assume tail:
        "Some (results, t) \<in> set_dist (execute ?tail s1)"
      and ret: "out \<in> set_dist (execute (return (u # results)) t)"
      and hit:
        "query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n) out"
  from ret obtain out_eq:
    "out = Some (u # results, t)"
    unfolding set_dist_def return.rep_eq dist_return_def
      dist_delta_dist delta_map_def
    by simp
    show "query_rounds_raw_list_path_hit s1 raws_tail n
        (Some (results, t))"
      by (rule query_rounds_raw_list_path_hit_tail
          [OF head[unfolded u_eq] tail])
        (use hit out_eq u_eq in simp)
  qed
qed

lemma wp_ntimes_verifier_query_round_program_raw_list_path_hit_bound:
  assumes len_raws: "length raws = n"
  shows
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n)
      (query_rounds_raw_list_path_hit s raws n) s \<le>
      (1 / nnreal size) ^ n"
  using len_raws
proof (induction n arbitrary: s raws)
  case 0
  then show ?case
    unfolding query_rounds_raw_list_path_hit_def
      query_index_list_path_fresh_def state_after_query_chunks_def
    by (simp add: wp_event_def wpsimps)
next
  case (Suc n)
  obtain raw raws_tail where raws_eq: "raws = raw # raws_tail"
    by (rule list_length_SucE[OF Suc.prems])
  have len_tail: "length raws_tail = n"
    using Suc.prems unfolding raws_eq by simp
  let ?prog = "verifier_query_round_program fr f_fl f_final as fl final"
  let ?tail =
    "ntimes ?prog n"
  let ?Q = "query_rounds_raw_list_path_hit s raws (Suc n)"
  let ?fresh =
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
  let ?Head =
    "\<lambda>out. ?fresh \<and> query_round_any_raw_set_hit s {raw} out"
  have head_bound:
    "wp_event ?prog ?Head s \<le> 1 / nnreal size"
  proof (cases ?fresh)
    case True
    have mono:
      "wp_event ?prog ?Head s \<le>
        wp_event ?prog (query_round_any_raw_set_hit s {raw}) s"
      by (rule wp_event_mono) simp
    also have "... \<le> nnreal (card {raw}) / nnreal size"
      by (rule wp_verifier_query_round_program_any_raw_set_bound[OF True])
    also have "... = 1 / nnreal size"
      by simp
    finally show ?thesis .
  next
    case False
    have impossible: "?Head = (\<lambda>_. False)"
      using False by auto
    have zero: "wp_event ?prog ?Head s = 0"
      by (simp only: impossible wp_event_false)
    then show ?thesis
      by simp
  qed
	  show ?case
	    unfolding ntimes.simps raws_eq
	  proof (rule order_trans)
	    have none_Q:
	      "\<not> query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n) None"
	      by (simp add: query_rounds_raw_list_path_hit_def)
	    show
	      "wp_event
	        (?prog \<bind> (\<lambda>u. ?tail \<bind> (\<lambda>xs. return (u # xs))))
	        (query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n)) s
	      \<le> wp_event ?prog ?Head s * ((1 / nnreal size) ^ n)"
	    proof (rule wp_event_bind_bound_by_head_and_cont
	        [where m = ?prog
	          and k = "\<lambda>u. ?tail \<bind> (\<lambda>xs. return (u # xs))"
	          and Q = "query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n)"
	          and P = ?Head
	          and D = "(1 / nnreal size) ^ n",
          OF none_Q])
		      fix u s1
		      assume head:
		        "Some (u, s1) \<in> set_dist (execute ?prog s)"
	        and not_head: "\<not> ?Head (Some (u, s1))"
	      show
	        "wp_event (?tail \<bind> (\<lambda>xs. return (u # xs)))
	          (query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n))
	          s1 = 0"
	      by (rule query_rounds_raw_list_path_hit_cont_zero_if_not_head
	          [OF head not_head])
	    next
	      fix u s1
	      assume head:
	        "Some (u, s1) \<in> set_dist (execute ?prog s)"
	        and head_hit: "?Head (Some (u, s1))"
	      have tail_bound:
	        "wp_event ?tail
	          (query_rounds_raw_list_path_hit s1 raws_tail n) s1 \<le>
          (1 / nnreal size) ^ n"
        by (rule Suc.IH[OF len_tail])
	      show
	        "wp_event (?tail \<bind> (\<lambda>xs. return (u # xs)))
	          (query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n))
	          s1 \<le> (1 / nnreal size) ^ n"
	      proof (rule order_trans[OF _ tail_bound])
	        show
	          "wp_event (?tail \<bind> (\<lambda>xs. return (u # xs)))
	            (query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n))
	            s1
	          \<le> wp_event ?tail
	            (query_rounds_raw_list_path_hit s1 raws_tail n) s1"
	        proof (rule wp_event_bind_return_cons_mono
	            [where m = ?tail
	              and Q =
	                "query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n)"
	              and R = "query_rounds_raw_list_path_hit s1 raws_tail n"
	              and u = u])
	          show
	            "query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n)
	              None \<Longrightarrow>
	             query_rounds_raw_list_path_hit s1 raws_tail n None"
	            unfolding query_rounds_raw_list_path_hit_def by simp
	        next
	          fix xs t
	          assume tail:
	              "Some (xs, t) \<in> set_dist (execute ?tail s1)"
	            and hit:
	              "query_rounds_raw_list_path_hit s (raw # raws_tail) (Suc n)
	                (Some (u # xs, t))"
	          have u_eq: "u = ()"
	            by (cases u) simp
	          show "query_rounds_raw_list_path_hit s1 raws_tail n
	            (Some (xs, t))"
	            by (rule query_rounds_raw_list_path_hit_tail
                [OF head[unfolded u_eq] tail])
	              (use hit u_eq in simp)
	        qed
	      qed
	    qed
  next
    show "wp_event ?prog ?Head s * (1 / nnreal size) ^ n
      \<le> (1 / nnreal size) ^ Suc n"
      using head_bound by (simp add: mult_right_mono)
  qed
qed

lemma wp_ntimes_verifier_query_round_program_raw_list_preimage_path_hit_bound:
  shows
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
        rounds)
      (\<lambda>out. \<exists>raws \<in> query_index_raw_list_preimage Q.
        query_rounds_raw_list_path_hit s raws rounds out)
      s \<le>
      nnreal (card (query_index_raw_list_preimage Q)) *
        (1 / nnreal size) ^ rounds"
proof -
  have finite_raws: "finite (query_index_raw_list_preimage Q)"
    by (rule finite_query_index_raw_list_preimage)
  have
    "wp_event
      (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
        rounds)
      (\<lambda>out. \<exists>raws \<in> query_index_raw_list_preimage Q.
        query_rounds_raw_list_path_hit s raws rounds out)
      s \<le>
      (\<Sum>raws \<in> query_index_raw_list_preimage Q.
        (1 / nnreal size) ^ rounds)"
    by (rule wp_event_finite_UN_bound[OF finite_raws])
      (rule wp_ntimes_verifier_query_round_program_raw_list_path_hit_bound,
        simp add: query_index_raw_list_preimage_def)
  also have "... =
      nnreal (card (query_index_raw_list_preimage Q)) *
        (1 / nnreal size) ^ rounds"
    using finite_raws by simp
  finally show ?thesis .
qed

lemma checked_staged_query_index_list_relation_fiber_card_bound:
  "card {y. checked_staged_query_index_list_relation A Q x y}
    \<le> query_index_raw_list_relation_fiber_bound Q"
proof -
  let ?values =
    "(\<Union>i < rounds. query_index_raw_list_position_values Q i)"
  have subset:
    "{y. checked_staged_query_index_list_relation A Q x y} \<subseteq> ?values"
    unfolding checked_staged_query_index_list_relation_def
      query_index_raw_list_position_values_def
    by blast
  have finite_values: "finite ?values"
    by simp
  have "card {y. checked_staged_query_index_list_relation A Q x y}
      \<le> card ?values"
    by (rule card_mono[OF finite_values subset])
  also have "... \<le>
      (\<Sum>i < rounds. card (query_index_raw_list_position_values Q i))"
    apply (rule card_UN_le) by simp
  also have "... = query_index_raw_list_relation_fiber_bound Q"
    unfolding query_index_raw_list_relation_fiber_bound_def by simp
  finally show ?thesis .
qed

lemma hash_relation_program_checked_staged_transcript_query_index_list:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_relation_program
      (checked_staged_query_index_list_relation A Q)
      (query_index_raw_list_relation_fiber_bound Q)
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)
      (checked_staged_transcript_program A)"
  by (rule hash_relation_program_checked_staged_transcript_program
      [OF wf controlled])
    (rule checked_staged_query_index_list_relation_fiber_card_bound)

lemma staged_transcript_query_index_list_set_hit_imp_relation_hit:
  assumes support:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    and hit:
      "staged_transcript_query_index_list_set_hit Q
        (Some (data, attacker_state))"
  shows
    "hash_relation_hit
      (checked_staged_query_index_list_relation A Q)
      adversary_initial_state attacker_state"
proof -
  from hit obtain raw_idxs query_idxs where
    len_raw: "length raw_idxs = rounds"
    and query_in: "query_idxs \<in> Q"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
          Some (raw_idxs ! i)"
    unfolding staged_transcript_query_index_list_set_hit_def by auto
  have raw_in: "raw_idxs \<in> query_index_raw_list_preimage Q"
    unfolding query_index_raw_list_preimage_def
    using len_raw query_in query_idxs_eq by blast
  let ?x =
    "QueryIndexChallenge 0
      (state_after_query_chunks
        (staged_query_start_hash data) (staged_query_chunks data) 0)"
  have zero_bound: "0 < rounds"
    by (rule rounds_positive)
  have initial_none: "fmlookup (HashMap adversary_initial_state) ?x = None"
    by (simp add: adversary_initial_state_def)
  have final_lookup:
    "fmlookup (HashMap attacker_state) ?x = Some (raw_idxs ! 0)"
    using lookup[OF zero_bound] by simp
  have rel:
    "checked_staged_query_index_list_relation A Q ?x (raw_idxs ! 0)"
    unfolding checked_staged_query_index_list_relation_def
    by (intro exI[of _ data] exI[of _ attacker_state]
        exI[of _ raw_idxs] exI[of _ 0] conjI)
      (use support raw_in zero_bound in simp_all)
	  show ?thesis
	    unfolding hash_relation_hit_def
	    by (intro exI[of _ ?x] exI[of _ "raw_idxs ! 0"] conjI)
	      (use initial_none final_lookup rel in simp_all)
qed

lemma staged_transcript_query_index_list_set_hit_imp_relation_hit_event:
  assumes support:
    "out \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    and hit: "staged_transcript_query_index_list_set_hit Q out"
  shows
    "hash_relation_hit_event
      (checked_staged_query_index_list_relation A Q)
      adversary_initial_state out"
proof (cases out)
  case None
  then show ?thesis
    using hit unfolding staged_transcript_query_index_list_set_hit_def
      hash_relation_hit_event_def
    by simp
next
  case (Some result)
  then obtain data attacker_state where out_eq:
    "out = Some (data, attacker_state)"
    by (cases result) simp
  have support_some:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    using support by (simp only: out_eq)
  have hit_some:
    "staged_transcript_query_index_list_set_hit Q
      (Some (data, attacker_state))"
    using hit by (simp only: out_eq)
  have rel_hit:
    "hash_relation_hit
      (checked_staged_query_index_list_relation A Q)
      adversary_initial_state attacker_state"
    by (rule staged_transcript_query_index_list_set_hit_imp_relation_hit
        [OF support_some hit_some])
  show ?thesis
    unfolding out_eq hash_relation_hit_event_def
    using rel_hit by simp
qed

lemma staged_transcript_query_index_list_set_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_transcript_program A)
      (staged_transcript_query_index_list_set_hit Q)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  have event_mono:
    "wp_event (checked_staged_transcript_program A)
      (staged_transcript_query_index_list_set_hit Q)
      adversary_initial_state \<le>
     wp_event (checked_staged_transcript_program A)
      (hash_relation_hit_event
        (checked_staged_query_index_list_relation A Q)
        adversary_initial_state)
      adversary_initial_state"
	  proof (rule wp_event_mono_on_support)
	    fix out
	    assume support:
	      "out \<in>
	        set_dist
	          (execute (checked_staged_transcript_program A)
	            adversary_initial_state)"
	      and hit: "staged_transcript_query_index_list_set_hit Q out"
	    show "hash_relation_hit_event
	      (checked_staged_query_index_list_relation A Q)
	      adversary_initial_state out"
	      by (rule staged_transcript_query_index_list_set_hit_imp_relation_hit_event
	          [OF support hit])
	  qed
  have relation_bound:
    "wp_event (checked_staged_transcript_program A)
      (hash_relation_hit_event
        (checked_staged_query_index_list_relation A Q)
        adversary_initial_state)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  proof -
    have program:
      "hash_relation_program
        (checked_staged_query_index_list_relation A Q)
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)
        (checked_staged_transcript_program A)"
      by (rule hash_relation_program_checked_staged_transcript_query_index_list
          [OF wf controlled])
    then show ?thesis
      unfolding hash_relation_program_def hash_relation_budget_def by blast
  qed
  show ?thesis
    by (rule order_trans[OF event_mono relation_bound])
qed

lemma checked_staged_security_with_data_query_index_list_set_bound_from_transcript:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and transcript_bound:
      "wp_event (checked_staged_transcript_program A)
        (staged_transcript_query_index_list_set_hit Q)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state \<le> C"
  unfolding checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_head_event[OF transcript_bound])
  show "staged_security_with_data_query_index_list_set_hit Q None \<Longrightarrow>
    staged_transcript_query_index_list_set_hit Q None"
    unfolding staged_security_with_data_query_index_list_set_hit_def
      staged_transcript_query_index_list_set_hit_def
    by simp
next
  fix data attacker_state out
  assume builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and cont:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>s. put
                (verifier_state_from_adversary s
                  (staged_proof_transcript data)) \<bind>
                (\<lambda>_.
                  verify_monad \<bind>
                    (\<lambda>result. return ((data, s), result)))))
            attacker_state)"
    and hit: "staged_security_with_data_query_index_list_set_hit Q out"
  from checked_staged_transcript_program_outcome_query_lookups
      [OF wf controlled builder]
  obtain attacker_raw_idxs attacker_query_idxs where
    len_attacker_raw: "length attacker_raw_idxs = rounds"
    and attacker_query_idxs_eq:
      "attacker_query_idxs =
        map (\<lambda>raw. index (to_nat raw)) attacker_raw_idxs"
    and lookup_attacker:
      "\<forall>j < rounds.
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
          Some (attacker_raw_idxs ! j)"
    by blast
  from hit obtain data' attacker_state' result final_state raw_idxs query_idxs where
    out_eq: "out = Some ((((data', attacker_state'), result), final_state))"
    and len_raw: "length raw_idxs = rounds"
    and query_in: "query_idxs \<in> Q"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup_final:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data')
              (staged_query_chunks data') i)) =
          Some (raw_idxs ! i)"
    unfolding staged_security_with_data_query_index_list_set_hit_def
    by (auto split: option.splits prod.splits)
  from cont[unfolded out_eq] obtain verifier_result where
    verifier:
      "Some (verifier_result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and data'_eq: "data' = data"
    and attacker_state'_eq: "attacker_state' = attacker_state"
    by (auto elim!: set_dist_bindE)
  have ext:
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data) \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  have raw_eq:
    "\<And>i. i < rounds \<Longrightarrow> attacker_raw_idxs ! i = raw_idxs ! i"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have lookup_initial:
      "fmlookup
        (HashMap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
        Some (attacker_raw_idxs ! i)"
      using lookup_attacker i_bound by simp
    have lookup_final_from_initial:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
        Some (attacker_raw_idxs ! i)"
      by (rule hash_extension_lookup[OF lookup_initial ext])
    show "attacker_raw_idxs ! i = raw_idxs ! i"
      using lookup_final_from_initial lookup_final[OF i_bound] data'_eq
      by simp
  qed
  have query_idxs_attacker:
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) attacker_raw_idxs"
  proof (rule nth_equalityI)
    show "length query_idxs =
      length (map (\<lambda>raw. index (to_nat raw)) attacker_raw_idxs)"
      using len_raw len_attacker_raw query_idxs_eq by simp
  next
    fix i
    assume i_bound:
      "i < length query_idxs"
    then have i_rounds: "i < rounds"
      using len_raw query_idxs_eq by simp
    then show "query_idxs ! i =
      map (\<lambda>raw. index (to_nat raw)) attacker_raw_idxs ! i"
      using query_idxs_eq raw_eq[OF i_rounds] len_raw apply simp
      using len_attacker_raw by auto
  qed
  show "staged_transcript_query_index_list_set_hit Q
      (Some (data, attacker_state))"
    unfolding staged_transcript_query_index_list_set_hit_def
    using len_attacker_raw query_in query_idxs_attacker lookup_attacker
    by auto
qed

lemma checked_staged_security_with_data_query_index_list_set_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule checked_staged_security_with_data_query_index_list_set_bound_from_transcript
      [OF wf controlled staged_transcript_query_index_list_set_hit_bound
        [OF wf controlled]])

lemma checked_staged_security_with_data_state_query_index_list_fresh_or_prequeried:
  assumes support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    and hit:
      "staged_security_with_data_query_index_list_set_hit Q
        (Some (((data, attacker_state), result), final_state))"
  shows
    "staged_security_with_data_state_query_index_list_path_fresh Q
      (Some (((data, attacker_state), result), final_state)) \<or>
     hash_relation_hit
      (checked_staged_query_index_list_relation A Q)
      adversary_initial_state attacker_state"
proof -
  from checked_staged_security_experiment_with_data_state_outcomeE[OF support]
  obtain builder verifier where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    by blast
  from hit obtain raw_idxs query_idxs where
    len_raw: "length raw_idxs = rounds"
    and query_in: "query_idxs \<in> Q"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup_final:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)"
    unfolding staged_security_with_data_query_index_list_set_hit_def
    by auto
  let ?vstate =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have raw_in: "raw_idxs \<in> query_index_raw_list_preimage Q"
    unfolding query_index_raw_list_preimage_def
    using len_raw query_in query_idxs_eq by blast
  have ext: "?vstate \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  show ?thesis
  proof (cases
      "\<forall>i < rounds.
        fmlookup (HashMap ?vstate)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        None")
    case True
    then have
      "staged_security_with_data_state_query_index_list_path_fresh Q
        (Some (((data, attacker_state), result), final_state))"
      unfolding staged_security_with_data_state_query_index_list_path_fresh_def
      using len_raw query_in query_idxs_eq lookup_final
      by (auto intro: exI[of _ raw_idxs] exI[of _ query_idxs])
    then show ?thesis by simp
  next
    case False
    then obtain i old where
      i_bound: "i < rounds"
      and lookup_initial:
        "fmlookup (HashMap ?vstate)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some old"
      by (metis option.exhaust)
    let ?key =
      "QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)"
    have lookup_final_old:
      "fmlookup (HashMap final_state) ?key = Some old"
      by (rule hash_extension_lookup[OF lookup_initial ext])
    have old_eq: "old = raw_idxs ! i"
      using lookup_final_old lookup_final[OF i_bound] by simp
    have lookup_attacker:
      "fmlookup (HashMap attacker_state) ?key = Some (raw_idxs ! i)"
      using lookup_initial old_eq
      unfolding verifier_state_from_adversary_def by simp
    have relation:
      "checked_staged_query_index_list_relation A Q ?key (raw_idxs ! i)"
      unfolding checked_staged_query_index_list_relation_def
      by (intro exI[of _ data] exI[of _ attacker_state]
          exI[of _ raw_idxs] exI[of _ i] conjI)
        (use builder raw_in i_bound in simp_all)
    have initial_none:
      "fmlookup (HashMap adversary_initial_state) ?key = None"
      by (simp add: adversary_initial_state_def)
    have
      "hash_relation_hit
        (checked_staged_query_index_list_relation A Q)
        adversary_initial_state attacker_state"
      unfolding hash_relation_hit_def
      by (intro exI[of _ ?key] exI[of _ "raw_idxs ! i"] conjI)
        (use initial_none lookup_attacker relation in simp_all)
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_data_state_query_index_list_prequery_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_index_list_prequery_hit A Q)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  unfolding checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_head_event)
  show "wp_event (checked_staged_transcript_program A)
      (hash_relation_hit_event
        (checked_staged_query_index_list_relation A Q)
        adversary_initial_state)
      adversary_initial_state
      \<le> hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
  proof -
    have program:
      "hash_relation_program
        (checked_staged_query_index_list_relation A Q)
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)
        (checked_staged_transcript_program A)"
      by (rule hash_relation_program_checked_staged_transcript_query_index_list
          [OF wf controlled])
    then show ?thesis
      unfolding hash_relation_program_def hash_relation_budget_def by blast
  qed
next
  show
    "staged_security_with_data_state_query_index_list_prequery_hit A Q None
      \<Longrightarrow>
     hash_relation_hit_event
      (checked_staged_query_index_list_relation A Q)
      adversary_initial_state None"
    unfolding staged_security_with_data_state_query_index_list_prequery_hit_def
      hash_relation_hit_event_def
    by simp
next
  fix data attacker_state out
  assume cont:
    "out \<in>
      set_dist
        (execute
          (get \<bind>
            (\<lambda>s. put
              (verifier_state_from_adversary s
                (staged_proof_transcript data)) \<bind>
              (\<lambda>_. verify_monad \<bind>
                (\<lambda>result. return ((data, s), result)))))
          attacker_state)"
  assume prequery:
    "staged_security_with_data_state_query_index_list_prequery_hit A Q out"
  show
    "hash_relation_hit_event
      (checked_staged_query_index_list_relation A Q)
      adversary_initial_state (Some (data, attacker_state))"
  proof (cases out)
    case None
    then show ?thesis
      using prequery
      unfolding staged_security_with_data_state_query_index_list_prequery_hit_def
      by simp
  next
    case (Some packed)
    from cont Some have cont_some:
      "Some packed \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>s. put
                (verifier_state_from_adversary s
                  (staged_proof_transcript data)) \<bind>
                (\<lambda>_. verify_monad \<bind>
                  (\<lambda>result. return ((data, s), result)))))
            attacker_state)"
      by simp
    obtain packed_value packed_state where packed_pair:
      "packed = (packed_value, packed_state)"
      by (cases packed)
    from cont_some[unfolded packed_pair] obtain captured get_state where get_out:
        "Some (captured, get_state) \<in> set_dist (execute get attacker_state)"
      and after_get0:
        "Some (packed_value, packed_state) \<in>
          set_dist
            (execute
              (put
                (verifier_state_from_adversary captured
                  (staged_proof_transcript data)) \<bind>
                (\<lambda>_. verify_monad \<bind>
                  (\<lambda>result. return ((data, captured), result))))
              get_state)"
      by (rule set_dist_bindE) (rule that)
    have captured_eq: "captured = attacker_state"
      and get_state_eq: "get_state = attacker_state"
      using get_out
      unfolding set_dist_def get.rep_eq dist_get_def
      by (simp_all add: dist_delta_dist delta_map_def)
    have after_get:
      "Some packed \<in>
        set_dist
          (execute
            (put
              (verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)) \<bind>
              (\<lambda>_. verify_monad \<bind>
                (\<lambda>result. return ((data, attacker_state), result))))
            attacker_state)"
      using after_get0 captured_eq get_state_eq packed_pair by simp
    from after_get[unfolded packed_pair] obtain unit put_state where put_out:
        "Some (unit, put_state) \<in>
          set_dist
            (execute
              (put
                (verifier_state_from_adversary attacker_state
                  (staged_proof_transcript data)))
              attacker_state)"
      and after_put0:
        "Some (packed_value, packed_state) \<in>
          set_dist
            (execute
              (verify_monad \<bind>
                (\<lambda>result. return ((data, attacker_state), result)))
              put_state)"
      by (rule set_dist_bindE) (rule that)
    have put_state_eq:
      "put_state =
        verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      using put_out
      unfolding set_dist_def put.rep_eq dist_put_def
      by (simp add: dist_delta_dist delta_map_def)
    have after_put:
      "Some packed \<in>
        set_dist
          (execute
            (verify_monad \<bind>
              (\<lambda>result. return ((data, attacker_state), result)))
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
      using after_put0 put_state_eq packed_pair by simp
    from after_put[unfolded packed_pair] obtain result final_state where verify_out:
        "Some (result, final_state) \<in>
          set_dist
            (execute verify_monad
              (verifier_state_from_adversary attacker_state
                (staged_proof_transcript data)))"
      and ret_out:
        "Some (packed_value, packed_state) \<in>
          set_dist (execute (return ((data, attacker_state), result)) final_state)"
      by (rule set_dist_bindE) (rule that)
    have packed_eq: "packed = (((data, attacker_state), result), final_state)"
    proof -
      have value_eq: "packed_value = ((data, attacker_state), result)"
        by (rule set_dist_return_valueD[OF ret_out])
      have state_eq: "packed_state = final_state"
        by (rule set_dist_return_stateD[OF ret_out])
      show ?thesis
        using packed_pair value_eq state_eq by simp
    qed
    have out_eq:
      "out = Some (((data, attacker_state), result), final_state)"
      using Some packed_eq by simp
    from prequery have hit:
      "hash_relation_hit
        (checked_staged_query_index_list_relation A Q)
        adversary_initial_state attacker_state"
      unfolding out_eq
        staged_security_with_data_state_query_index_list_prequery_hit_def
      by simp
    then show ?thesis
      using hit unfolding hash_relation_hit_event_def by simp
  qed
qed

lemma checked_staged_security_with_data_state_query_index_list_hit_bound_from_path_fresh:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and path_fresh_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_path_fresh Q)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  have event_mono:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_with_data_state_query_index_list_path_fresh Q out \<or>
        staged_security_with_data_state_query_index_list_prequery_hit A Q out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit: "staged_security_with_data_query_index_list_set_hit Q out"
    show
      "staged_security_with_data_state_query_index_list_path_fresh Q out \<or>
       staged_security_with_data_state_query_index_list_prequery_hit A Q out"
    proof (cases out)
      case None
      then show ?thesis
        using hit unfolding staged_security_with_data_query_index_list_set_hit_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed) (auto split: prod.splits)
      have split:
        "staged_security_with_data_state_query_index_list_path_fresh Q
          (Some (((data, attacker_state), result), final_state)) \<or>
         hash_relation_hit
          (checked_staged_query_index_list_relation A Q)
          adversary_initial_state attacker_state"
        apply (rule
            checked_staged_security_with_data_state_query_index_list_fresh_or_prequeried)
        using support hit unfolding out_eq by simp_all
      then show ?thesis
        unfolding out_eq
          staged_security_with_data_state_query_index_list_prequery_hit_def
        by simp
    qed
  qed
  have union_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_with_data_state_query_index_list_path_fresh Q out \<or>
        staged_security_with_data_state_query_index_list_prequery_hit A Q out)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_path_fresh Q)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_prequery_hit A Q)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  have prequery_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_index_list_prequery_hit A Q)
      adversary_initial_state \<le>
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule
        checked_staged_security_with_data_state_query_index_list_prequery_hit_bound
        [OF wf controlled])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_path_fresh Q)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_prequery_hit A Q)
        adversary_initial_state"
    by (rule order_trans[OF event_mono union_bound])
  also have "... \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule add_mono[OF path_fresh_bound prequery_bound])
  finally show ?thesis .
qed

lemma accepted_fri_opening_transcript_imp_accepted_transcript_shape:
  assumes fri:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
  shows "\<exists>as. accepted_transcript_shape s out as query_idxs"
  using fri
  unfolding accepted_fri_opening_transcript_def
    accepted_transcript_shape_def
  by blast

lemma checked_staged_security_trace_fri_query_index_list_set_hit_bound_list:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state \<le>
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule order_trans)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit:
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q) out"
    show "staged_security_with_data_query_index_list_set_hit Q out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding staged_security_with_data_state_verifier_event_def
          staged_security_with_data_query_index_list_set_hit_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed) (auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from hit out_eq have trace_hit:
        "trace_fri_query_index_list_set_hit ?s Q
          (Some (result, final_state))"
        unfolding staged_security_with_data_state_verifier_event_def by simp
      from trace_hit obtain trace_roots trace_bs trace_final dg
          composition_roots composition_bs composition_final query_idxs
          trace_round_layers composition_round_layers where
        fri:
          "accepted_fri_opening_transcript ?s (Some (result, final_state))
            trace_roots trace_bs trace_final dg composition_roots
            composition_bs composition_final query_idxs trace_round_layers
            composition_round_layers"
        and query_in: "query_idxs \<in> Q"
        unfolding trace_fri_query_index_list_set_hit_def by blast
      from accepted_fri_opening_transcript_imp_accepted_transcript_shape[OF fri]
      obtain as where shape:
        "accepted_transcript_shape ?s (Some (result, final_state)) as
          query_idxs"
        by blast
      from checked_staged_security_with_data_state_accepted_shape_query_keys
          [OF wf controlled support[unfolded out_eq] shape]
      obtain raw_idxs where
        len_raw: "length raw_idxs = rounds"
        and query_idxs_eq:
          "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
        and lookup:
          "\<And>i. i < rounds \<Longrightarrow>
            fmlookup (HashMap final_state)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
            Some (raw_idxs ! i)"
        by blast
      show ?thesis
        unfolding out_eq staged_security_with_data_query_index_list_set_hit_def
        using len_raw query_in query_idxs_eq lookup by auto
    qed
  qed
next
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state
      \<le> hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule checked_staged_security_with_data_query_index_list_set_hit_bound
        [OF wf controlled])
qed

lemma checked_staged_security_composition_fri_query_index_list_set_hit_bound_list:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state \<le>
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule order_trans)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit:
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q) out"
    show "staged_security_with_data_query_index_list_set_hit Q out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding staged_security_with_data_state_verifier_event_def
          staged_security_with_data_query_index_list_set_hit_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed) (auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from hit out_eq have composition_hit:
        "composition_fri_query_index_list_set_hit ?s Q
          (Some (result, final_state))"
        unfolding staged_security_with_data_state_verifier_event_def by simp
      from composition_hit obtain trace_roots trace_bs trace_final dg
          composition_roots composition_bs composition_final query_idxs
          trace_round_layers composition_round_layers where
        fri:
          "accepted_fri_opening_transcript ?s (Some (result, final_state))
            trace_roots trace_bs trace_final dg composition_roots
            composition_bs composition_final query_idxs trace_round_layers
            composition_round_layers"
        and query_in: "query_idxs \<in> Q"
        unfolding composition_fri_query_index_list_set_hit_def by blast
      from accepted_fri_opening_transcript_imp_accepted_transcript_shape[OF fri]
      obtain as where shape:
        "accepted_transcript_shape ?s (Some (result, final_state)) as
          query_idxs"
        by blast
      from checked_staged_security_with_data_state_accepted_shape_query_keys
          [OF wf controlled support[unfolded out_eq] shape]
      obtain raw_idxs where
        len_raw: "length raw_idxs = rounds"
        and query_idxs_eq:
          "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
        and lookup:
          "\<And>i. i < rounds \<Longrightarrow>
            fmlookup (HashMap final_state)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
            Some (raw_idxs ! i)"
        by blast
      show ?thesis
        unfolding out_eq staged_security_with_data_query_index_list_set_hit_def
        using len_raw query_in query_idxs_eq lookup by auto
    qed
  qed
next
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state
      \<le> hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule checked_staged_security_with_data_query_index_list_set_hit_bound
        [OF wf controlled])
qed

lemma checked_staged_security_trace_fri_query_challenge_pair_set_hit_bound_list:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and projection: "fst ` P \<subseteq> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule order_trans)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          trace_fri_query_challenge_pair_set_hit_imp_query_index_list_set_hit
            [OF _ projection]
        split: option.splits prod.splits)
next
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state
      \<le> hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule checked_staged_security_trace_fri_query_index_list_set_hit_bound_list
        [OF wf controlled])
qed

lemma checked_staged_security_composition_fri_query_challenge_pair_set_hit_bound_list:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and projection: "\<And>dg. fst ` P dg \<subseteq> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule order_trans)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_fri_query_challenge_pair_set_hit_imp_query_index_list_set_hit
            [OF _ projection]
        split: option.splits prod.splits)
next
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state
      \<le> hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule
        checked_staged_security_composition_fri_query_index_list_set_hit_bound_list
        [OF wf controlled])
qed

lemma checked_staged_security_trace_fri_query_index_list_set_hit_bound_from_path_fresh:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and path_fresh_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_path_fresh Q)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule order_trans)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit:
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q) out"
    show "staged_security_with_data_query_index_list_set_hit Q out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding staged_security_with_data_state_verifier_event_def
          staged_security_with_data_query_index_list_set_hit_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed) (auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from hit out_eq have trace_hit:
        "trace_fri_query_index_list_set_hit ?s Q
          (Some (result, final_state))"
        unfolding staged_security_with_data_state_verifier_event_def by simp
      from trace_hit obtain trace_roots trace_bs trace_final dg
          composition_roots composition_bs composition_final query_idxs
          trace_round_layers composition_round_layers where
        fri:
          "accepted_fri_opening_transcript ?s (Some (result, final_state))
            trace_roots trace_bs trace_final dg composition_roots
            composition_bs composition_final query_idxs trace_round_layers
            composition_round_layers"
        and query_in: "query_idxs \<in> Q"
        unfolding trace_fri_query_index_list_set_hit_def by blast
      from accepted_fri_opening_transcript_imp_accepted_transcript_shape[OF fri]
      obtain as where shape:
        "accepted_transcript_shape ?s (Some (result, final_state)) as
          query_idxs"
        by blast
      from checked_staged_security_with_data_state_accepted_shape_query_keys
          [OF wf controlled support[unfolded out_eq] shape]
      obtain raw_idxs where
        len_raw: "length raw_idxs = rounds"
        and query_idxs_eq:
          "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
        and lookup:
          "\<And>i. i < rounds \<Longrightarrow>
            fmlookup (HashMap final_state)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
            Some (raw_idxs ! i)"
        by blast
      show ?thesis
        unfolding out_eq staged_security_with_data_query_index_list_set_hit_def
        using len_raw query_in query_idxs_eq lookup by auto
    qed
  qed
next
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state
      \<le> C +
        hash_relation_budget_value
          (query_index_raw_list_relation_fiber_bound Q)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_with_data_state_query_index_list_hit_bound_from_path_fresh
        [OF wf controlled path_fresh_bound])
qed

lemma checked_staged_security_composition_fri_query_index_list_set_hit_bound_from_path_fresh:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and path_fresh_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_path_fresh Q)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule order_trans)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit:
      "staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q) out"
    show "staged_security_with_data_query_index_list_set_hit Q out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding staged_security_with_data_state_verifier_event_def
          staged_security_with_data_query_index_list_set_hit_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed) (auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from hit out_eq have composition_hit:
        "composition_fri_query_index_list_set_hit ?s Q
          (Some (result, final_state))"
        unfolding staged_security_with_data_state_verifier_event_def by simp
      from composition_hit obtain trace_roots trace_bs trace_final dg
          composition_roots composition_bs composition_final query_idxs
          trace_round_layers composition_round_layers where
        fri:
          "accepted_fri_opening_transcript ?s (Some (result, final_state))
            trace_roots trace_bs trace_final dg composition_roots
            composition_bs composition_final query_idxs trace_round_layers
            composition_round_layers"
        and query_in: "query_idxs \<in> Q"
        unfolding composition_fri_query_index_list_set_hit_def by blast
      from accepted_fri_opening_transcript_imp_accepted_transcript_shape[OF fri]
      obtain as where shape:
        "accepted_transcript_shape ?s (Some (result, final_state)) as
          query_idxs"
        by blast
      from checked_staged_security_with_data_state_accepted_shape_query_keys
          [OF wf controlled support[unfolded out_eq] shape]
      obtain raw_idxs where
        len_raw: "length raw_idxs = rounds"
        and query_idxs_eq:
          "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
        and lookup:
          "\<And>i. i < rounds \<Longrightarrow>
            fmlookup (HashMap final_state)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
            Some (raw_idxs ! i)"
        by blast
      show ?thesis
        unfolding out_eq staged_security_with_data_query_index_list_set_hit_def
        using len_raw query_in query_idxs_eq lookup by auto
    qed
  qed
next
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_query_index_list_set_hit Q)
      adversary_initial_state
      \<le> C +
        hash_relation_budget_value
          (query_index_raw_list_relation_fiber_bound Q)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_with_data_state_query_index_list_hit_bound_from_path_fresh
        [OF wf controlled path_fresh_bound])
qed

lemma checked_staged_security_trace_fri_query_challenge_pair_set_hit_bound_from_path_fresh:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and projection: "fst ` P \<subseteq> Q"
    and path_fresh_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_path_fresh Q)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule order_trans)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          trace_fri_query_challenge_pair_set_hit_imp_query_index_list_set_hit
            [OF _ projection]
        split: option.splits prod.splits)
next
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state
      \<le> C +
        hash_relation_budget_value
          (query_index_raw_list_relation_fiber_bound Q)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_query_index_list_set_hit_bound_from_path_fresh
        [OF wf controlled path_fresh_bound])
qed

lemma checked_staged_security_composition_fri_query_challenge_pair_set_hit_bound_from_path_fresh:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and projection: "\<And>dg. fst ` P dg \<subseteq> Q"
    and path_fresh_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_index_list_path_fresh Q)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule order_trans)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_fri_query_challenge_pair_set_hit_imp_query_index_list_set_hit
            [OF _ projection]
        split: option.splits prod.splits)
next
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state
      \<le> C +
        hash_relation_budget_value
          (query_index_raw_list_relation_fiber_bound Q)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
    by (rule
        checked_staged_security_composition_fri_query_index_list_set_hit_bound_from_path_fresh
        [OF wf controlled path_fresh_bound])
qed

end

end
