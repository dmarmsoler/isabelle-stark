theory Soundness_FRI_Query_Future_Count
  imports Soundness_FRI_Query_Future_Fresh_Zero_Budget
begin

context soundness
begin

definition hash_map_new_key_count
  :: "'f protocol_channel \<Rightarrow> 'f protocol_channel \<Rightarrow> nat"
where
  "hash_map_new_key_count s t =
    card (fmdom' (HashMap t) - fmdom' (HashMap s))"

lemma hash_map_new_key_count_hash_le_one:
  assumes outcome:
    "Some (y, t) \<in>
      set_dist (execute (hash x :: ('f, 'f protocol_channel) state_monad) s)"
  shows "hash_map_new_key_count s t \<le> 1"
proof -
  have t_eq:
      "t = s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>"
    by (rule hash_output_state[OF outcome])
  have dom_subset:
      "fmdom' (HashMap t) - fmdom' (HashMap s) \<subseteq> {x}"
    unfolding t_eq by auto
  show ?thesis
    unfolding hash_map_new_key_count_def
    using card_mono[OF _ dom_subset]
    by simp
qed

lemma hash_map_new_key_count_trans_le:
  "hash_map_new_key_count s t \<le>
    hash_map_new_key_count s u + hash_map_new_key_count u t"
proof -
  let ?A = "fmdom' (HashMap u) - fmdom' (HashMap s)"
  let ?B = "fmdom' (HashMap t) - fmdom' (HashMap u)"
  have subset:
      "fmdom' (HashMap t) - fmdom' (HashMap s) \<subseteq> ?A \<union> ?B"
    by blast
  have card_subset:
      "card (fmdom' (HashMap t) - fmdom' (HashMap s))
        \<le> card (?A \<union> ?B)"
    by (rule card_mono[OF _ subset]) simp
  have "card (?A \<union> ?B) \<le> card ?A + card ?B"
    by (rule card_Un_le)
  with card_subset show ?thesis
    unfolding hash_map_new_key_count_def by linarith
qed

lemma hash_map_preserving_new_key_count_zero:
  assumes preserving: "hash_map_preserving m"
    and outcome: "Some (x, t) \<in> set_dist (execute m s)"
  shows "hash_map_new_key_count s t = 0"
proof -
  have same: "HashMap t = HashMap s"
    using preserving outcome
    unfolding hash_map_preserving_def by blast
  show ?thesis
    unfolding hash_map_new_key_count_def same by simp
qed

lemma controlled_ro_program_new_key_count_bound:
  assumes controlled: "controlled_ro_program q m"
    and outcome: "Some (result, t) \<in> set_dist (execute m s)"
  shows "hash_map_new_key_count s t \<le> q"
  using controlled outcome
proof (induction arbitrary: s result t rule: controlled_ro_program.induct)
  case (Return x)
  then show ?case
    unfolding hash_map_new_key_count_def by simp
next
  case Fail
  then show ?case
    by (simp add: throw_no_outcome)
next
  case (Sample d)
  have zero: "hash_map_new_key_count s t = 0"
    by (rule hash_map_preserving_new_key_count_zero[
          OF hash_map_preserving_state_independent_sample Sample.prems])
  then show ?case by simp
next
  case (Query q k key)
  from Query.prems obtain y u where
    hash_out:
      "Some (y, u) \<in>
        set_dist
          (execute (hash key :: ('f, 'f protocol_channel) state_monad) s)"
    and tail_out:
      "Some (result, t) \<in> set_dist (execute (k y) u)"
    by (auto elim!: set_dist_bindE)
  have head: "hash_map_new_key_count s u \<le> 1"
    by (rule hash_map_new_key_count_hash_le_one[OF hash_out])
  have tail: "hash_map_new_key_count u t \<le> q"
    using Query.IH tail_out by blast
  have trans:
      "hash_map_new_key_count s t \<le>
        hash_map_new_key_count s u + hash_map_new_key_count u t"
    by (rule hash_map_new_key_count_trans_le)
  show ?case
    using trans head tail by linarith
next
  case (Bind q m r k)
  from Bind.prems obtain x u where
    head_out: "Some (x, u) \<in> set_dist (execute m s)"
    and tail_out: "Some (result, t) \<in> set_dist (execute (k x) u)"
    by (auto elim!: set_dist_bindE)
  have head: "hash_map_new_key_count s u \<le> q"
    by (rule Bind.IH(1)[OF head_out])
  have tail: "hash_map_new_key_count u t \<le> r"
    using Bind.IH(2) tail_out by blast
  have trans:
      "hash_map_new_key_count s t \<le>
        hash_map_new_key_count s u + hash_map_new_key_count u t"
    by (rule hash_map_new_key_count_trans_le)
  show ?case
    using trans head tail by linarith
next
  case (Weaken q m r)
  have "hash_map_new_key_count s t \<le> q"
    by (rule Weaken.IH[OF Weaken.prems])
  then show ?case
    using Weaken.hyps(2) by linarith
qed


definition query_future_keys
  :: "'f protocol_channel \<Rightarrow> 'f protocol_hash_input set"
where
  "query_future_keys s =
    {key \<in> fmdom' (HashMap s).
      \<exists>i x. PQueryCounter s \<le> i \<and> key = QueryIndexChallenge i x}"

definition query_future_prequery_count :: "'f protocol_channel \<Rightarrow> nat"
where
  "query_future_prequery_count s = card (query_future_keys s)"

lemma finite_query_future_keys[simp]: "finite (query_future_keys s)"
  unfolding query_future_keys_def
  by (rule finite_subset[of _ "fmdom' (HashMap s)"]) auto

lemma controlled_ro_program_query_future_prequery_count_bound:
  assumes controlled: "controlled_ro_program q m"
    and outcome: "Some (result, t) \<in> set_dist (execute m s)"
  shows
    "query_future_prequery_count t \<le>
      query_future_prequery_count s + q"
proof -
  have counter_eq: "PQueryCounter t = PQueryCounter s"
    using controlled_ro_program_preserves_protocol_fields[OF controlled]
      outcome
    unfolding protocol_fields_preserving_def by blast
  let ?N = "fmdom' (HashMap t) - fmdom' (HashMap s)"
  have subset:
      "query_future_keys t \<subseteq> query_future_keys s \<union> ?N"
    unfolding query_future_keys_def counter_eq by blast
  have card_subset:
      "card (query_future_keys t) \<le> card (query_future_keys s \<union> ?N)"
    by (rule card_mono[OF _ subset]) simp
  have union_bound:
      "card (query_future_keys s \<union> ?N) \<le>
        card (query_future_keys s) + card ?N"
    by (rule card_Un_le)
  have new_bound: "card ?N \<le> q"
    using controlled_ro_program_new_key_count_bound[OF controlled outcome]
    unfolding hash_map_new_key_count_def .
  show ?thesis
    unfolding query_future_prequery_count_def
    using card_subset union_bound new_bound by linarith
qed

lemma receive_query_index_challenge_future_keys_subset:
  assumes outcome:
    "Some (raw, t) \<in> set_dist (execute receive_query_index_challenge s)"
  shows "query_future_keys t \<subseteq> query_future_keys s"
proof
  fix key
  assume key_t: "key \<in> query_future_keys t"
  then obtain i x y where
    lookup_t: "fmlookup (HashMap t) key = Some y"
    and i_ge: "PQueryCounter t \<le> i"
    and key_eq: "key = QueryIndexChallenge i x"
    unfolding query_future_keys_def fmlookup_dom'_iff by blast
  have counter:
      "PQueryCounter t = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF outcome] by simp
  have neq:
      "key \<noteq> QueryIndexChallenge (PQueryCounter s) (PState s)"
    using i_ge counter key_eq by auto
  have lookup_eq:
      "fmlookup (HashMap t) key = fmlookup (HashMap s) key"
    by (rule receive_query_index_challenge_preserves_other_lookup[
          OF outcome neq])
  have lookup_s: "fmlookup (HashMap s) key = Some y"
    using lookup_t lookup_eq by simp
  have key_dom_s: "key \<in> fmdom' (HashMap s)"
    by (rule fmdom'I[OF lookup_s])
  have old_ge: "PQueryCounter s \<le> i"
    using i_ge counter by simp
  show "key \<in> query_future_keys s"
    unfolding query_future_keys_def
    using key_dom_s old_ge key_eq by blast
qed


lemma receive_query_index_challenge_future_count_le:
  assumes outcome:
    "Some (raw, t) \<in> set_dist (execute receive_query_index_challenge s)"
  shows "query_future_prequery_count t \<le> query_future_prequery_count s"
  unfolding query_future_prequery_count_def
  by (rule card_mono[OF finite_query_future_keys
        receive_query_index_challenge_future_keys_subset[OF outcome]])

lemma receive_query_index_challenge_known_future_count_Suc_le:
  assumes known:
      "fmlookup (HashMap s)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some old_raw"
    and outcome:
      "Some (raw, t) \<in> set_dist (execute receive_query_index_challenge s)"
  shows
    "Suc (query_future_prequery_count t) \<le>
      query_future_prequery_count s"
proof -
  let ?key = "QueryIndexChallenge (PQueryCounter s) (PState s)"
  have counter:
      "PQueryCounter t = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF outcome] by simp
  have current_dom: "?key \<in> fmdom' (HashMap s)"
    by (rule fmdom'I[OF known])
  have current_s: "?key \<in> query_future_keys s"
    unfolding query_future_keys_def
    using current_dom by blast
  have current_not_t: "?key \<notin> query_future_keys t"
    unfolding query_future_keys_def
    using counter by auto
  have subset: "query_future_keys t \<union> {?key} \<subseteq> query_future_keys s"
    using receive_query_index_challenge_future_keys_subset[OF outcome]
      current_s by blast
  have card_union:
      "card (query_future_keys t \<union> {?key}) =
        Suc (card (query_future_keys t))"
    using current_not_t by simp
  have card_le:
      "card (query_future_keys t \<union> {?key}) \<le> card (query_future_keys s)"
    by (rule card_mono[OF finite_query_future_keys subset])
  show ?thesis
    unfolding query_future_prequery_count_def
    using card_union card_le by simp
qed

lemma ro_record_staged_message_query_future_keys_eq:
  assumes outcome:
    "Some ((), t) \<in> set_dist (execute (ro_record_staged_message a) s)"
  shows "query_future_keys t = query_future_keys s"
proof -
  from ro_record_staged_message_outcome[OF outcome]
  obtain h u where
    hash_out:
      "Some (h, u) \<in>
        set_dist (execute (hash (TranscriptAbsorb (PState s) a)) s)"
    and t_eq:
      "t = u\<lparr>PState := h, PTranscript := PTranscript u @ [a]\<rparr>"
    and counter_eq: "PQueryCounter u = PQueryCounter s"
    by blast
  have lookup_eq:
    "\<And>i x. fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s) (QueryIndexChallenge i x)"
  proof -
    fix i x
    have neq:
      "QueryIndexChallenge i x \<noteq> TranscriptAbsorb (PState s) a"
      by simp
    show
      "fmlookup (HashMap t) (QueryIndexChallenge i x) =
        fmlookup (HashMap s) (QueryIndexChallenge i x)"
      using protocol_hash_preserves_other_lookup[OF hash_out neq]
      unfolding t_eq by simp
  qed
  have counter: "PQueryCounter t = PQueryCounter s"
    unfolding t_eq using counter_eq by simp
  show ?thesis
  proof (rule equalityI)
    show "query_future_keys t \<subseteq> query_future_keys s"
    proof
      fix key
      assume key_t: "key \<in> query_future_keys t"
      then obtain i x where
        i_ge: "PQueryCounter t \<le> i"
        and key_eq: "key = QueryIndexChallenge i x"
        unfolding query_future_keys_def by blast
      from key_t obtain y where
        lookup_t: "fmlookup (HashMap t) key = Some y"
        unfolding query_future_keys_def fmlookup_dom'_iff by blast
      have lookup_s: "fmlookup (HashMap s) key = Some y"
        using lookup_eq[of i x] lookup_t unfolding key_eq by simp
      have key_dom_s: "key \<in> fmdom' (HashMap s)"
        by (rule fmdom'I[OF lookup_s])
      show "key \<in> query_future_keys s"
        unfolding query_future_keys_def
        using key_dom_s i_ge key_eq counter by simp
    qed
  next
    show "query_future_keys s \<subseteq> query_future_keys t"
    proof
      fix key
      assume key_s: "key \<in> query_future_keys s"
      then obtain i x where
        i_ge: "PQueryCounter s \<le> i"
        and key_eq: "key = QueryIndexChallenge i x"
        unfolding query_future_keys_def by blast
      from key_s obtain y where
        lookup_s: "fmlookup (HashMap s) key = Some y"
        unfolding query_future_keys_def fmlookup_dom'_iff by blast
      have lookup_t: "fmlookup (HashMap t) key = Some y"
        using lookup_eq[of i x] lookup_s unfolding key_eq by simp
      have key_dom_t: "key \<in> fmdom' (HashMap t)"
        by (rule fmdom'I[OF lookup_t])
      show "key \<in> query_future_keys t"
        unfolding query_future_keys_def
        using key_dom_t i_ge key_eq counter by simp
    qed
  qed
qed


lemma ro_record_staged_message_query_future_prequery_count_eq:
  assumes outcome:
    "Some ((), t) \<in> set_dist (execute (ro_record_staged_message a) s)"
  shows
    "query_future_prequery_count t = query_future_prequery_count s"
  unfolding query_future_prequery_count_def
  using ro_record_staged_message_query_future_keys_eq[OF outcome]
  by simp

lemma ro_record_staged_messages_query_future_prequery_count_eq:
  assumes outcome:
    "Some ((), t) \<in>
      set_dist (execute (ro_record_staged_messages xs) s)"
  shows
    "query_future_prequery_count t = query_future_prequery_count s"
  using outcome
proof (induction xs arbitrary: s t)
  case Nil
  then show ?case
    unfolding ro_record_staged_messages_def by simp
next
  case (Cons x xs)
  from Cons.prems obtain u where
    head:
      "Some ((), u) \<in>
        set_dist (execute (ro_record_staged_message x) s)"
    and tail:
      "Some ((), t) \<in>
        set_dist (execute (ro_record_staged_messages xs) u)"
    unfolding ro_record_staged_messages_def
    by (auto elim!: set_dist_bindE)
  have head_eq:
    "query_future_prequery_count u = query_future_prequery_count s"
    by (rule ro_record_staged_message_query_future_prequery_count_eq[OF head])
  have tail_eq:
    "query_future_prequery_count t = query_future_prequery_count u"
    by (rule Cons.IH[OF tail])
  show ?case
    using head_eq tail_eq by simp
qed

end
end
