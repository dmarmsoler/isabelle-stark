(*  License: BSD-3-Clause *)
theory RO_Honest_Verifier_Replay
  imports "Stark.RO_Honest_Replay_Primitives"
begin

section \<open>Exact Replay of RO Verifier Reads\<close>

text \<open>Exact weakest-precondition equalities account for failure as well as successful outcomes. Recorded lookups determine message absorption and counted challenges, including the residual transcript and complete channel state. These are local correctness helpers, not additional soundness premises.\<close>

lemma protocol_absorb_read_known_wp:
  assumes tr: "PTranscript s = x # xs"
    and known: "fmlookup (HashMap s) (TranscriptAbsorb (PState s) x) = Some next"
  shows "wp protocol_absorb_read Q s =
    Q (Some (x,s\<lparr>PState := next, PTranscript := xs\<rparr>))"
  unfolding protocol_absorb_read_def
  by (simp add: wp_bind wp_get wp_modify wp_return assert_def tr hash_known_wp[OF known])

lemma protocol_counted_challenge_known_wp:
  assumes known: "fmlookup (HashMap s) (tag (counter s) (PState s)) = Some b"
  shows "wp (protocol_receive_counted_tagged_random_field_element counter bump tag) Q s =
    Q (Some (b,bump s))"
  unfolding protocol_receive_counted_tagged_random_field_element_def
  by (simp add: wp_bind wp_get wp_modify wp_return hash_known_wp[OF known])

lemma ro_recorded_messages_exact_replay:
  fixes sent s :: "'f::finite protocol_channel"
  assumes chain: "ro_absorb_lookup_chain sent start xs final"
    and ext: "sent \<le> s"
    and cursor: "PState s = start"
    and transcript: "PTranscript s = xs @ rest"
  shows "wp (ntimes protocol_absorb_read (length xs)) Q s =
    Q (Some (xs,s\<lparr>PState := final, PTranscript := rest\<rparr>))"
  using chain ext cursor transcript
proof (induction xs arbitrary: start s Q)
  case Nil
  then show ?case
    apply (simp add: wp_return)
    by fastforce
next
  case (Cons x xs)
  then obtain nxt where key:
    "fmlookup (HashMap sent) (TranscriptAbsorb start x) = Some nxt"
    and tail: "ro_absorb_lookup_chain sent nxt xs final" by auto
  have known: "fmlookup (HashMap s) (TranscriptAbsorb (PState s) x) = Some nxt"
    using protocol_merkle.hash_extension_lookup[OF key Cons.prems(2)] Cons.prems(3) by simp
  let ?t = "s\<lparr>PState := nxt,PTranscript := xs @ rest\<rparr>"
  have ext: "sent \<le> ?t"
    using Cons.prems(2) by (simp add: less_eq_hash_ext_def)
  have step: "wp protocol_absorb_read Q' s = Q' (Some (x,?t))" for Q'
    by (rule protocol_absorb_read_known_wp[OF _ known]) (use Cons.prems(4) in simp)
  show ?case
    by (simp add: wp_bind wp_return step Cons.IH[OF tail ext])
qed


lemma ro_absorb_lookup_chain_append_iff:
  "ro_absorb_lookup_chain s start (xs @ ys) final \<longleftrightarrow>
    (\<exists>mid. ro_absorb_lookup_chain s start xs mid \<and>
      ro_absorb_lookup_chain s mid ys final)"
  by (induction xs arbitrary: start) auto

lemma protocol_absorb_read_leaf_path_wp:
  fixes s sent :: "'f::finite protocol_channel"
  assumes chain: "ro_absorb_lookup_chain sent (PState s) (leaf # path) final"
    and ext: "sent \<le> s"
    and tr: "PTranscript s = (leaf # path) @ rest"
    and len: "length path=n"
  shows "wp (protocol_absorb_read \<bind> (\<lambda>v.
    ntimes protocol_absorb_read n \<bind> (\<lambda>ap. return (v,ap)))) Q s =
    Q (Some ((leaf,path),s\<lparr>PState := final,PTranscript := rest\<rparr>))"
proof -
  obtain mid where key:
    "fmlookup (HashMap sent) (TranscriptAbsorb (PState s) leaf)=Some mid"
    and tail: "ro_absorb_lookup_chain sent mid path final" using chain by auto
  have known: "fmlookup (HashMap s) (TranscriptAbsorb (PState s) leaf)=Some mid"
    by (rule protocol_merkle.hash_extension_lookup[OF key ext])
  let ?t = "s\<lparr>PState := mid,PTranscript := path@rest\<rparr>"
  have ext': "sent \<le> ?t" using ext by (simp add: less_eq_hash_ext_def)
  have head: "wp protocol_absorb_read F s=F (Some (leaf,?t))" for F
    by (rule protocol_absorb_read_known_wp[OF _ known]) (use tr in simp)
  have tail: "wp (ntimes protocol_absorb_read n) F ?t =
    F (Some (path,s\<lparr>PState := final,PTranscript := rest\<rparr>))" for F
    using ro_recorded_messages_exact_replay[OF tail ext', of rest F] len by simp
  show ?thesis by (simp add: wp_bind wp_return head tail)
qed

context soundness
begin

lemma receive_trace_fri_challenge_known_wp:
  assumes "fmlookup (HashMap s) (TraceFriChallenge (PTraceFriCounter s) (PState s)) = Some b"
  shows "wp receive_trace_fri_challenge Q s =
    Q (Some (b,s\<lparr>PTraceFriCounter := Suc (PTraceFriCounter s)\<rparr>))"
  unfolding receive_trace_fri_challenge_def
  by (rule protocol_counted_challenge_known_wp) (rule assms)

lemma receive_composition_fri_challenge_known_wp:
  assumes "fmlookup (HashMap s) (CompositionFriChallenge (PCompositionFriCounter s) (PState s)) = Some b"
  shows "wp receive_composition_fri_challenge Q s =
    Q (Some (b,s\<lparr>PCompositionFriCounter := Suc (PCompositionFriCounter s)\<rparr>))"
  unfolding receive_composition_fri_challenge_def
  by (rule protocol_counted_challenge_known_wp) (rule assms)

lemma receive_alpha_challenge_known_wp:
  assumes "fmlookup (HashMap s) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some b"
  shows "wp receive_alpha_challenge Q s =
    Q (Some (b,s\<lparr>PAlphaCounter := Suc (PAlphaCounter s)\<rparr>))"
  unfolding receive_alpha_challenge_def
  by (rule protocol_counted_challenge_known_wp) (rule assms)

lemma receive_query_index_challenge_known_wp:
  assumes "fmlookup (HashMap s) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some b"
  shows "wp receive_query_index_challenge Q s =
    Q (Some (b,s\<lparr>PQueryCounter := Suc (PQueryCounter s)\<rparr>))"
  unfolding receive_query_index_challenge_def
  by (rule protocol_counted_challenge_known_wp) (rule assms)


lemma ro_recorded_messages_actual_wp:
  assumes recorded: "Some ((),sent) \<in> set_dist (execute (ro_record_staged_messages xs) builder)"
    and ext: "sent \<le> s"
    and cursor: "PState s=PState builder"
    and transcript: "PTranscript s=xs@rest"
  shows "wp (ntimes protocol_absorb_read (length xs)) Q s =
    Q (Some (xs,s\<lparr>PState := PState sent,PTranscript := rest\<rparr>))"
  by (rule ro_recorded_messages_exact_replay[OF
    conjunct1[OF ro_record_staged_messages_absorb_lookup_chain[OF recorded]]
    ext cursor transcript])

lemma ro_receive_trace_fri_commits_known_wp:
  fixes root :: "'f"
  assumes tr: "PTranscript s=root#rest"
    and absorb: "fmlookup (HashMap s) (TranscriptAbsorb (PState s) root)=Some cursor"
    and challenge: "fmlookup (HashMap s) (TraceFriChallenge (PTraceFriCounter s) cursor)=Some b"
  shows "wp ro_receive_trace_fri_commits Q s=
    Q (Some ((b,root),s\<lparr>PState := cursor,PTranscript := rest,
      PTraceFriCounter := Suc (PTraceFriCounter s)\<rparr>))"
proof -
  have ch: "fmlookup (HashMap (s\<lparr>PState := cursor,PTranscript := rest\<rparr>))
    (TraceFriChallenge (PTraceFriCounter (s\<lparr>PState := cursor,PTranscript := rest\<rparr>))
      (PState (s\<lparr>PState := cursor,PTranscript := rest\<rparr>)))=Some b"
    using challenge by simp
  show ?thesis
    unfolding ro_receive_trace_fri_commits_def ro_receive_fri_commits_with_def
    by (simp add: wp_bind wp_return protocol_absorb_read_known_wp[OF tr absorb]
      receive_trace_fri_challenge_known_wp[OF ch])
qed

lemma ro_receive_composition_fri_commits_known_wp:
  fixes root :: "'f"
  assumes tr: "PTranscript s=root#rest"
    and absorb: "fmlookup (HashMap s) (TranscriptAbsorb (PState s) root)=Some cursor"
    and challenge: "fmlookup (HashMap s) (CompositionFriChallenge (PCompositionFriCounter s) cursor)=Some b"
  shows "wp ro_receive_composition_fri_commits Q s=
    Q (Some ((b,root),s\<lparr>PState := cursor,PTranscript := rest,
      PCompositionFriCounter := Suc (PCompositionFriCounter s)\<rparr>))"
proof -
  have ch: "fmlookup (HashMap (s\<lparr>PState := cursor,PTranscript := rest\<rparr>))
    (CompositionFriChallenge (PCompositionFriCounter (s\<lparr>PState := cursor,PTranscript := rest\<rparr>))
      (PState (s\<lparr>PState := cursor,PTranscript := rest\<rparr>)))=Some b"
    using challenge by simp
  show ?thesis
    unfolding ro_receive_composition_fri_commits_def ro_receive_fri_commits_with_def
    by (simp add: wp_bind wp_return protocol_absorb_read_known_wp[OF tr absorb]
      receive_composition_fri_challenge_known_wp[OF ch])
qed

lemma ro_alpha_round_known_wp:
  assumes tr: "PTranscript s=a#rest"
    and challenge: "fmlookup (HashMap s) (AlphaChallenge (PAlphaCounter s) (PState s))=Some a"
    and absorb: "fmlookup (HashMap s) (TranscriptAbsorb (PState s) a)=Some cursor"
  shows "wp ro_alpha_round Q s=
    Q (Some (a,s\<lparr>PAlphaCounter := Suc (PAlphaCounter s),
      PState := cursor,PTranscript := rest\<rparr>))"
proof -
  have tr': "PTranscript (s\<lparr>PAlphaCounter := Suc (PAlphaCounter s)\<rparr>)=a#rest" using tr by simp
  have key: "fmlookup (HashMap (s\<lparr>PAlphaCounter := Suc (PAlphaCounter s)\<rparr>))
    (TranscriptAbsorb (PState (s\<lparr>PAlphaCounter := Suc (PAlphaCounter s)\<rparr>)) a)=Some cursor"
    using absorb by simp
  show ?thesis unfolding ro_alpha_round_def
    by (simp add: wp_bind wp_return Let_def assert_def
      receive_alpha_challenge_known_wp[OF challenge]
      protocol_absorb_read_known_wp[OF tr' key])
qed

end
end
