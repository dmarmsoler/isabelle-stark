(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Exact.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Exact
  imports Soundness_FRI_RO_Actual_Query_Trace_Composition_Sampled_Bound
begin

context soundness
begin

definition ro_alpha_vector_key_relation
  :: "'f protocol_channel \<Rightarrow> 'f list set \<Rightarrow> nat \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "ro_alpha_vector_key_relation s B n x y \<longleftrightarrow>
    (\<exists>as \<in> B. \<exists>i < n. \<exists>st.
      i < length as \<and>
      x = AlphaChallenge (PAlphaCounter s + i) st \<and>
      y = as ! i)"


definition ro_alpha_vector_prequeried_in_state
  :: "'f protocol_channel \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> bool"
where
  "ro_alpha_vector_prequeried_in_state s as n \<longleftrightarrow>
    (\<exists>i < n. \<exists>st.
      i < length as \<and>
      fmlookup (HashMap s)
        (AlphaChallenge (PAlphaCounter s + i) st) = Some (as ! i))"

lemma ro_alpha_vector_key_relation_fiber_card_bound:
  assumes finite_B: "finite B"
  shows "card {y. ro_alpha_vector_key_relation s B n x y} \<le> card B * n"
proof -
  let ?pairs = "B \<times> {..<n}"
  let ?values = "image (\<lambda>(as, i). as ! i) ?pairs"
  have subset:
      "{y. ro_alpha_vector_key_relation s B n x y} \<subseteq> ?values"
    unfolding ro_alpha_vector_key_relation_def
    by force
  have finite_values: "finite ?values"
    using finite_B by simp
  have "card {y. ro_alpha_vector_key_relation s B n x y} \<le> card ?values"
    by (rule card_mono[OF finite_values subset])
  also have "... \<le> card ?pairs"
    by (rule card_image_le) (use finite_B in simp)
  also have "... = card B * n"
    using finite_B by simp
  finally show ?thesis .
qed

lemma wp_receive_alpha_challenge_exact_value_le_if_not_prequeried:
  fixes s :: "'f protocol_channel"
  assumes absent:
    "fmlookup (HashMap s)
      (AlphaChallenge (PAlphaCounter s) (PState s)) \<noteq> Some a"
  shows
    "wp_event receive_alpha_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (a', _) \<Rightarrow> a' = a) s
      \<le> 1 / nnreal size"
proof (cases "fmlookup (HashMap s)
    (AlphaChallenge (PAlphaCounter s) (PState s)) = None")
  case True
  have exact:
    "wp_event receive_alpha_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (a', _) \<Rightarrow> a' \<in> {a}) s =
      nnreal (card ({a} :: 'f set)) / nnreal size"
    by (rule wp_receive_alpha_challenge_fresh_set[OF True])
  have event_eq:
    "(\<lambda>out :: ('f \<times> 'f protocol_channel) option.
        case out of None \<Rightarrow> False | Some (a', _) \<Rightarrow> a' \<in> {a}) =
     (\<lambda>out. case out of None \<Rightarrow> False | Some (a', _) \<Rightarrow> a' = a)"
    by (rule ext) (auto split: option.splits prod.splits)
  have desired:
    "wp_event receive_alpha_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (a', _) \<Rightarrow> a' = a) s =
      1 / nnreal size"
    using exact unfolding event_eq by simp
  then show ?thesis by simp
next
  case False
  then obtain old where lookup:
    "fmlookup (HashMap s)
      (AlphaChallenge (PAlphaCounter s) (PState s)) = Some old"
    by (cases "fmlookup (HashMap s)
      (AlphaChallenge (PAlphaCounter s) (PState s))") auto
  have old_ne: "old \<noteq> a"
    using absent lookup by simp
  have le_zero:
    "wp_event receive_alpha_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (a', _) \<Rightarrow> a' = a) s
      \<le>
     wp_event receive_alpha_challenge (\<lambda>_. False) s"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute receive_alpha_challenge s)"
      and hit:
        "(case out of None \<Rightarrow> False | Some (a', _) \<Rightarrow> a' = a)"
    show False
    proof (cases out)
      case None
      then show ?thesis using hit by simp
    next
      case (Some pair)
      then obtain a' t where out_eq: "out = Some (a', t)"
        by (cases pair) simp
      have outcome:
        "Some (a', t) \<in> set_dist (execute receive_alpha_challenge s)"
        using support unfolding out_eq .
      have known: "a' = old"
        using receive_alpha_challenge_known_outcome[OF lookup outcome]
        by simp
      show ?thesis
        using hit known old_ne unfolding out_eq by simp
    qed
  qed
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally have zero:
    "wp_event receive_alpha_challenge
      (\<lambda>out. case out of None \<Rightarrow> False | Some (a', _) \<Rightarrow> a' = a) s
      \<le> 0" .
  show ?thesis
    by (rule order_trans[OF zero]) simp
qed
lemma ro_alpha_vector_not_prequeried_Cons_tail:
  fixes s t u :: "'f protocol_channel"
  assumes not_pre:
      "\<not> ro_alpha_vector_prequeried_in_state s (a # as) (Suc n)"
    and recv:
      "Some (a, t) \<in> set_dist (execute receive_alpha_challenge s)"
    and record_out:
      "Some ((), u) \<in> set_dist (execute (ro_record_staged_message a) t)"
  shows "\<not> ro_alpha_vector_prequeried_in_state u as n"
proof
  assume pre: "ro_alpha_vector_prequeried_in_state u as n"
  from pre obtain i st where
    i_n: "i < n"
    and i_len: "i < length as"
    and lookup_u:
      "fmlookup (HashMap u)
        (AlphaChallenge (PAlphaCounter u + i) st) = Some (as ! i)"
    unfolding ro_alpha_vector_prequeried_in_state_def
    by blast
  let ?K = "AlphaChallenge (PAlphaCounter u + i) st"
  have recv_counters:
      "PAlphaCounter t = Suc (PAlphaCounter s)"
    using receive_alpha_challenge_counter_outcome[OF recv]
    by simp
  have record_out_counters:
      "PAlphaCounter u = PAlphaCounter t"
    using ro_record_staged_message_counter_preserves[OF record_out]
    by simp
  obtain h v where
    hash_out:
      "Some (h, v) \<in>
        set_dist (execute (hash (TranscriptAbsorb (PState t) a)) t)"
    and u_eq:
      "u = v\<lparr>PState := h, PTranscript := PTranscript v @ [a]\<rparr>"
  proof (rule ro_record_staged_message_outcome[OF record_out])
    fix h v
    assume hash_out':
        "Some (h, v) \<in>
          set_dist (execute (hash (TranscriptAbsorb (PState t) a)) t)"
      and u_eq':
        "u = v\<lparr>PState := h, PTranscript := PTranscript v @ [a]\<rparr>"
      and "PState v = PState t"
      and "PTranscript v = PTranscript t"
      and "PTraceFriCounter v = PTraceFriCounter t"
      and "PCompositionFriCounter v = PCompositionFriCounter t"
      and "PAlphaCounter v = PAlphaCounter t"
      and "PQueryCounter v = PQueryCounter t"
      and "t \<le> v"
    show ?thesis
      by (rule that[OF hash_out' u_eq'])
  qed
  have key_ne_absorb:
      "?K \<noteq> TranscriptAbsorb (PState t) a"
    by simp
  have lookup_v:
      "fmlookup (HashMap v) ?K = Some (as ! i)"
    using lookup_u unfolding u_eq by simp
  have lookup_t:
      "fmlookup (HashMap t) ?K = Some (as ! i)"
    using protocol_hash_preserves_other_lookup[OF hash_out key_ne_absorb]
      lookup_v
    by simp
  have key_ne_head:
      "?K \<noteq> AlphaChallenge (PAlphaCounter s) (PState s)"
    using recv_counters record_out_counters i_n by simp
  have lookup_s:
      "fmlookup (HashMap s) ?K = Some (as ! i)"
    using receive_alpha_challenge_preserves_other_lookup[
        OF recv key_ne_head]
      lookup_t
    by simp
  have key_eq:
      "?K = AlphaChallenge (PAlphaCounter s + Suc i) st"
    using recv_counters record_out_counters by simp
  have initial_pre:
      "ro_alpha_vector_prequeried_in_state s (a # as) (Suc n)"
    unfolding ro_alpha_vector_prequeried_in_state_def
  proof (intro exI conjI)
    show "Suc i < Suc n"
      using i_n by simp
    show "Suc i < length (a # as)"
      using i_len by simp
    show
      "fmlookup (HashMap s)
        (AlphaChallenge (PAlphaCounter s + Suc i) st) =
          Some ((a # as) ! Suc i)"
      using lookup_s key_eq by simp
  qed
  show False
    using not_pre initial_pre by contradiction
qed

lemma wp_ro_staged_alpha_program_exact_vector_bound_if_not_prequeried:
  fixes s :: "'f protocol_channel"
  assumes len: "length as = n"
    and not_pre: "\<not> ro_alpha_vector_prequeried_in_state s as n"
  shows
    "wp_event (ro_staged_alpha_program n)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as', _) \<Rightarrow> as' = as) s
      \<le> (1 / nnreal size) ^ n"
  using len not_pre
proof (induction n arbitrary: as s)
  case 0
  then have as_empty: "as = []"
    by simp
  show ?case
    unfolding as_empty by (simp add: wp_event_def wpsimps)
next
  case (Suc n)
  obtain a as_tail where as_eq: "as = a # as_tail"
    using Suc.prems(1) by (cases as) auto
  have len_tail: "length as_tail = n"
    using Suc.prems(1) as_eq by simp
  let ?tail =
    "ro_staged_alpha_program n ::
      ('f list, 'f protocol_channel) state_monad"
  let ?Q =
    "\<lambda>out :: ('f list \<times> 'f protocol_channel) option.
      case out of None \<Rightarrow> False | Some (as', _) \<Rightarrow> as' = as"
  let ?Head =
    "\<lambda>out :: ('f \<times> 'f protocol_channel) option.
      case out of None \<Rightarrow> False | Some (a0, _) \<Rightarrow> a0 = a"
  have head_not_pre:
      "fmlookup (HashMap s)
        (AlphaChallenge (PAlphaCounter s) (PState s)) \<noteq> Some a"
  proof
    assume lookup:
      "fmlookup (HashMap s)
        (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    have "ro_alpha_vector_prequeried_in_state s (a # as_tail) (Suc n)"
      unfolding ro_alpha_vector_prequeried_in_state_def
      apply (rule exI[of _ 0])
      apply simp
      apply (rule exI[of _ "PState s"])
      using lookup by simp
    then show False
      using Suc.prems(2) unfolding as_eq by contradiction
  qed
  have head_bound:
      "wp_event receive_alpha_challenge ?Head s \<le> 1 / nnreal size"
    by (rule wp_receive_alpha_challenge_exact_value_le_if_not_prequeried[
          OF head_not_pre])
  have bind_bound:
    "wp_event
      (receive_alpha_challenge \<bind>
        (\<lambda>a0. ro_record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind>
            (\<lambda>as'. return (a0 # as')))))
      ?Q s
      \<le> wp_event receive_alpha_challenge ?Head s *
        (1 / nnreal size) ^ n"
  proof (rule wp_event_bind_bound_by_head_and_cont[where P = ?Head])
    show "\<not> ?Q None"
      by simp
  next
    fix a0 t
    assume recv:
        "Some (a0, t) \<in> set_dist (execute receive_alpha_challenge s)"
      and not_head: "\<not> ?Head (Some (a0, t))"
    have a0_ne: "a0 \<noteq> a"
      using not_head by simp
    have cont_false:
      "wp_event
        (ro_record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t
       \<le>
       wp_event
        (ro_record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        (\<lambda>_ :: ('f list \<times> 'f protocol_channel) option. False) t"
      by (rule wp_event_mono_on_support)
        (use a0_ne as_eq in
          \<open>auto simp: wpsimps elim!: set_dist_bindE
              split: option.splits prod.splits\<close>)
    also have "... = 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
    finally have le_zero:
      "wp_event
        (ro_record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t \<le> 0" .
    show
      "wp_event
        (ro_record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t = 0"
      by (rule antisym[OF le_zero]) simp
  next
    fix a0 t
    assume recv:
        "Some (a0, t) \<in> set_dist (execute receive_alpha_challenge s)"
      and head: "?Head (Some (a0, t))"
    have a0_eq: "a0 = a"
      using head by simp
    have record_cont_bound:
      "wp_event
        (ro_record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t
        \<le> (1 / nnreal size) ^ n"
    proof (rule wp_event_bind_bound_by_cont)
      show "\<not> ?Q None"
        by simp
    next
      fix uu u
      assume record_out:
        "Some (uu, u) \<in>
          set_dist (execute (ro_record_staged_message a0) t)"
      have record_unit:
        "Some ((), u) \<in>
          set_dist (execute (ro_record_staged_message a0) t)"
        using record_out by (cases uu) simp
      have tail_not_pre:
          "\<not> ro_alpha_vector_prequeried_in_state u as_tail n"
      proof -
        have initial:
            "\<not> ro_alpha_vector_prequeried_in_state
              s (a # as_tail) (Suc n)"
          using Suc.prems(2) unfolding as_eq .
        have recv_a:
            "Some (a, t) \<in>
              set_dist (execute receive_alpha_challenge s)"
          using recv a0_eq by simp
        have record_a:
            "Some ((), u) \<in>
              set_dist (execute (ro_record_staged_message a) t)"
          using record_unit a0_eq by simp
        show ?thesis
          by (rule ro_alpha_vector_not_prequeried_Cons_tail[
                OF initial recv_a record_a])
      qed
      have tail_bound:
        "wp_event ?tail
          (\<lambda>out. case out of None \<Rightarrow> False
            | Some (as', _) \<Rightarrow> as' = as_tail) u
          \<le> (1 / nnreal size) ^ n"
        by (rule Suc.IH[OF len_tail tail_not_pre])
      have cont_eq:
        "wp_event
          (?tail \<bind> (\<lambda>as'. return (a0 # as'))) ?Q u =
         wp_event ?tail
          (\<lambda>out. case out of None \<Rightarrow> False
            | Some (as', _) \<Rightarrow> as' = as_tail) u"
        by (simp add: wp_event_bind_return_map a0_eq as_eq
            split: option.splits prod.splits)
      show
        "wp_event (?tail \<bind> (\<lambda>as'. return (a0 # as'))) ?Q u
          \<le> (1 / nnreal size) ^ n"
        unfolding cont_eq by (rule tail_bound)
    qed
    show
      "wp_event
        (ro_record_staged_message a0 \<bind>
          (\<lambda>_. ?tail \<bind> (\<lambda>as'. return (a0 # as'))))
        ?Q t
        \<le> (1 / nnreal size) ^ n"
      by (rule record_cont_bound)
  qed
  have
    "wp_event (ro_staged_alpha_program (Suc n)) ?Q s
      \<le> wp_event receive_alpha_challenge ?Head s *
        (1 / nnreal size) ^ n"
    unfolding ro_staged_alpha_program.simps by (rule bind_bound)
  also have "... \<le> (1 / nnreal size) * (1 / nnreal size) ^ n"
    by (rule mult_right_mono[OF head_bound]) simp
  also have "... = (1 / nnreal size) ^ Suc n"
    by simp
  finally show ?case .
qed

lemma wp_ro_staged_alpha_program_finite_set_bound_if_not_prequeried:
  fixes s :: "'f protocol_channel"
  assumes finite_B: "finite B"
    and lengths: "\<And>as. as \<in> B \<Longrightarrow> length as = n"
    and not_pre:
      "\<And>as. as \<in> B \<Longrightarrow>
        \<not> ro_alpha_vector_prequeried_in_state s as n"
  shows
    "wp_event (ro_staged_alpha_program n)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s
      \<le> nnreal (card B) / (nnreal size) ^ n"
proof -
  let ?P =
    "\<lambda>a out. case out of None \<Rightarrow> False
      | Some (as', _) \<Rightarrow> as' = a"
  have event_mono:
    "wp_event (ro_staged_alpha_program n)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s
      \<le>
     wp_event (ro_staged_alpha_program n)
      (\<lambda>out. \<exists>as\<in>B. ?P as out) s"
    by (rule wp_event_mono) (auto split: option.splits prod.splits)
  also have "... \<le>
      (\<Sum>a\<in>B. wp_event (ro_staged_alpha_program n) (?P a) s)"
    by (rule wp_event_finite_UN_bound[where A = B and P = ?P])
      (use finite_B in simp_all)
  also have "... \<le> (\<Sum>as\<in>B. (1 / nnreal size) ^ n)"
  proof (rule sum_mono)
    fix as
    assume as_in: "as \<in> B"
    show
      "wp_event (ro_staged_alpha_program n) (?P as) s
        \<le> (1 / nnreal size) ^ n"
      by (rule
          wp_ro_staged_alpha_program_exact_vector_bound_if_not_prequeried[
            OF lengths[OF as_in] not_pre[OF as_in]])
  qed
  also have "... = nnreal (card B) * ((1 / nnreal size) ^ n)"
    using finite_B by simp
  also have "... = nnreal (card B) / (nnreal size) ^ n"
    using size_card by transfer (simp add: power_divide)
  finally show ?thesis .
qed

lemma wp_ro_staged_alpha_program_bad_set_bound_if_not_prequeried:
  fixes s :: "'f protocol_channel"
  assumes subset: "B \<subseteq> alpha_space"
    and not_pre:
      "\<And>as. as \<in> B \<Longrightarrow>
        \<not> ro_alpha_vector_prequeried_in_state s as (length spec)"
  shows
    "wp_event (ro_staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s
      \<le> nnreal (card B) / nnreal (CARD('f) ^ length spec)"
proof -
  have finite_B: "finite B"
    by (rule finite_subset[OF subset])
      (simp add: alpha_space_def finite_length_lists_UNIV)
  have lengths:
      "\<And>as. as \<in> B \<Longrightarrow> length as = length spec"
    using subset unfolding alpha_space_def by auto
  have bound:
    "wp_event (ro_staged_alpha_program (length spec))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (as, _) \<Rightarrow> as \<in> B) s
      \<le> nnreal (card B) / (nnreal size) ^ length spec"
    by (rule wp_ro_staged_alpha_program_finite_set_bound_if_not_prequeried[
          OF finite_B lengths not_pre])
  show ?thesis
    using bound size_card by simp
qed

end
end
