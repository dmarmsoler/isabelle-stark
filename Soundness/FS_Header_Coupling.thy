(* Title: Stark/FS_Header_Coupling.thy
   License: BSD-3-Clause *)

theory FS_Header_Coupling
  imports FS_Query_Phase_Prescan
begin

section \<open>Chronological header read and record coupling\<close>

text \<open>This proof-side relation compares the existing reader and recorder over
  every initial channel, oracle cache, transcript suffix and postcondition.
  Recording appends words whereas reading consumes them; the final relation
  restores only the unread transcript. Cursor, counters and the complete oracle
  map agree. Failure mass is retained without a freshness or clean-map premise.\<close>

context soundness
begin

definition fs_header_coupling
  :: "'f list \<Rightarrow> ('a,'f protocol_channel) state_monad \<Rightarrow>
    ('a,'f protocol_channel) state_monad \<Rightarrow> bool"
where
  "fs_header_coupling xs reader writer \<longleftrightarrow>
    (\<forall>s rest F. wp reader F (s\<lparr>PTranscript:=xs@rest\<rparr>) =
      wp writer (\<lambda>out. case out of None \<Rightarrow> F None
        | Some(x,t) \<Rightarrow> F(Some(x,t\<lparr>PTranscript:=rest\<rparr>))) s)"

lemma fs_header_coupling_return:
  "fs_header_coupling [] (return x) (return x)"
  by (simp add: fs_header_coupling_def wp_return)

lemma fs_header_coupling_bind:
  assumes first: "fs_header_coupling xs reader writer"
    and tail: "\<And>x. fs_header_coupling ys (k x) (l x)"
  shows "fs_header_coupling (xs@ys) (reader \<bind> k) (writer \<bind> l)"
  using first tail
  by (auto simp: fs_header_coupling_def wp_bind
    cong: option.case_cong prod.case_cong)

lemma fs_header_coupling_bind_mapped:
  assumes first: "fs_header_coupling xs reader (writer \<bind> (\<lambda>x. return(map_value x)))"
    and tail: "\<And>x. fs_header_coupling ys (k(map_value x)) (l x)"
  shows "fs_header_coupling (xs@ys) (reader \<bind> k) (writer \<bind> l)"
  using first tail
  by (auto simp: fs_header_coupling_def wp_bind wp_return
    cong: option.case_cong prod.case_cong)

lemma fs_header_coupling_read:
  "fs_header_coupling [x] protocol_absorb_read
    (ro_record_staged_message x \<bind> (\<lambda>_. return x))"
  by (simp add: fs_header_coupling_def protocol_absorb_read_def
    ro_record_staged_message_def wp_bind wp_get wp_hash wp_modify
    wp_return wp_throw assert_def hash_dist_def)

lemma fs_header_coupling_trace_challenge:
  "fs_header_coupling [] receive_trace_fri_challenge receive_trace_fri_challenge"
  apply (simp add: fs_header_coupling_def receive_trace_fri_challenge_def
    protocol_receive_counted_tagged_random_field_element_def
    wp_bind wp_get wp_hash wp_modify wp_return hash_dist_def)
  by (intro allI, rename_tac s rest F, case_tac s) simp

lemma fs_header_coupling_composition_challenge:
  "fs_header_coupling [] receive_composition_fri_challenge receive_composition_fri_challenge"
  unfolding fs_header_coupling_def
  by (intro allI, rename_tac s rest F, case_tac s)
    (simp add: receive_composition_fri_challenge_def
      protocol_receive_counted_tagged_random_field_element_def
      wp_bind wp_get wp_hash wp_modify wp_return hash_dist_def)

lemma fs_header_coupling_alpha_challenge:
  "fs_header_coupling [] receive_alpha_challenge receive_alpha_challenge"
  unfolding fs_header_coupling_def
  by (intro allI, rename_tac s rest F, case_tac s)
    (simp add: receive_alpha_challenge_def
      protocol_receive_counted_tagged_random_field_element_def
      wp_bind wp_get wp_hash wp_modify wp_return hash_dist_def)

lemma fs_header_coupling_assert:
  "fs_header_coupling [] (assert P) (assert P)"
  by (simp add: fs_header_coupling_def assert_def wp_return wp_throw)

lemma fs_wp_const:
  "wp m (\<lambda>_. c) s=c"
  by (simp add: wp_def fs_expect_const)

lemma fs_header_coupling_fail:
  "fs_header_coupling xs throw throw"
  by (simp add: fs_header_coupling_def wp_throw)


lemma fs_header_coupling_read_bind:
  assumes tail: "fs_header_coupling xs (k x) writer"
  shows "fs_header_coupling (x#xs) (protocol_absorb_read \<bind> k)
    (ro_record_staged_message x \<bind> (\<lambda>_. writer))"
proof (unfold fs_header_coupling_def, intro allI)
  fix s rest F
  have rw: "wp protocol_absorb_read G (s\<lparr>PTranscript:=x#ys\<rparr>) =
    wp (ro_record_staged_message x)
      (\<lambda>out. case out of None \<Rightarrow> G None
       | Some(_,t) \<Rightarrow> G(Some(x,t\<lparr>PTranscript:=ys\<rparr>))) s" for G ys
    using fs_header_coupling_read[of x]
    by (simp add: fs_header_coupling_def wp_bind wp_return
      cong: option.case_cong prod.case_cong)
  show "wp (protocol_absorb_read \<bind> k) F (s\<lparr>PTranscript:=(x#xs)@rest\<rparr>) =
    wp (ro_record_staged_message x \<bind> (\<lambda>_. writer))
     (\<lambda>out. case out of None \<Rightarrow> F None | Some(y,t) \<Rightarrow> F(Some(y,t\<lparr>PTranscript:=rest\<rparr>))) s"
    using tail unfolding fs_header_coupling_def
    by (simp add: wp_bind rw cong: option.case_cong prod.case_cong)
qed

lemma fs_option_const [simp]:
  "(case out of None \<Rightarrow> c | Some _ \<Rightarrow> c)=c"
  by (cases out) simp_all

lemma fs_throw_after:
  "(m \<bind> (\<lambda>_. throw))=throw"
  by (rule fs_wp_ext)
    (simp add: wp_bind wp_throw fs_wp_const
      cong: option.case_cong prod.case_cong)

primrec fs_header_write_fri
  :: "('f,'f protocol_channel) state_monad \<Rightarrow> 'f list \<Rightarrow>
    ('f list,'f protocol_channel) state_monad"
where
  "fs_header_write_fri recv [] = return []"
| "fs_header_write_fri recv (r#rs) =
    (ro_record_staged_message r \<bind> (\<lambda>_. recv \<bind> (\<lambda>b.
      fs_header_write_fri recv rs \<bind> (\<lambda>bs. return(b#bs)))))"

lemma fs_header_coupling_fri:
  assumes recv: "fs_header_coupling [] receive receive"
  shows "fs_header_coupling rs
    (ntimes (ro_receive_fri_commits_with receive) (length rs))
    (fs_header_write_fri receive rs \<bind> (\<lambda>bs. return(zip bs rs)))"
proof (induction rs)
  case Nil
  show ?case by (simp add: fs_header_coupling_return)
next
  case (Cons r rs)
  show ?case
    unfolding length_Cons ntimes.simps ro_receive_fri_commits_with_def
      fs_header_write_fri.simps sm_bind_assoc sm_bind_return_left
    apply (rule fs_header_coupling_read_bind)
    apply (rule fs_header_coupling_bind[where xs="[]", simplified, OF recv])
    apply (simp only: zip_Cons_Cons)
    apply (rule fs_header_coupling_bind[where ys="[]", simplified,
      OF Cons.IH[unfolded ro_receive_fri_commits_with_def],
      unfolded sm_bind_assoc sm_bind_return_left])
    apply (rule fs_header_coupling_return)
    done
qed

definition fs_header_guarded_alphas where
  "fs_header_guarded_alphas supplied =
    (ro_staged_alpha_program (length supplied) \<bind> (\<lambda>actual.
      assert(actual=supplied) \<bind> (\<lambda>_. return actual)))"

lemma fs_header_guarded_alphas_Nil:
  "fs_header_guarded_alphas []=return []"
  by (simp add: fs_header_guarded_alphas_def assert_def)

lemma fs_header_guarded_alphas_Cons:
  "fs_header_guarded_alphas (x#xs) =
   (receive_alpha_challenge \<bind> (\<lambda>a.
     if a=x then ro_record_staged_message x \<bind> (\<lambda>_.
       fs_header_guarded_alphas xs \<bind> (\<lambda>as. return(x#as)))
     else throw))"
  unfolding fs_header_guarded_alphas_def length_Cons
    ro_staged_alpha_program.simps sm_bind_assoc sm_bind_return_left
  by (rule arg_cong[where f="\<lambda>k. receive_alpha_challenge \<bind> k"], rule ext)
    (simp add: assert_def sm_bind_assoc fs_throw_after fs_throw_bind split: if_splits)


text \<open>The existing builder generates all alpha echoes before the degree
  callback can reject them. The following equality retains the verifier's
  failure probability even though a mismatching reader rejects earlier. Failed
  states are unobservable in the existing option-valued monad.\<close>

lemma fs_header_coupling_alphas:
  "fs_header_coupling supplied
    (mmap(replicate(length supplied) ro_alpha_round))
    (fs_header_guarded_alphas supplied)"
proof (induction supplied)
  case Nil
  show ?case by (simp add: fs_header_guarded_alphas_Nil fs_header_coupling_return)
next
  case (Cons x xs)
  let ?tail = "mmap(replicate(length xs) ro_alpha_round)"
  let ?k = "\<lambda>a y. assert(a=y) \<bind> (\<lambda>_. ?tail \<bind> (\<lambda>as. return(y#as)))"
  have body: "fs_header_coupling (x#xs)
    (protocol_absorb_read \<bind> ?k a)
    (if a=x then ro_record_staged_message x \<bind> (\<lambda>_.
      fs_header_guarded_alphas xs \<bind> (\<lambda>as. return(x#as))) else throw)" for a
  proof (cases "a=x")
    case True
    have tail: "fs_header_coupling xs (?k a x)
      (fs_header_guarded_alphas xs \<bind> (\<lambda>as. return(x#as)))"
      using True
      by (simp add: assert_def)
        (rule fs_header_coupling_bind[where ys="[]", simplified, OF Cons.IH],
          rule fs_header_coupling_return)
    show ?thesis using fs_header_coupling_read_bind[where k="?k a" and x=x, OF tail] True by simp
  next
    case False
    have tail: "fs_header_coupling xs (?k a x) throw"
      using False by (simp add: assert_def fs_throw_bind fs_header_coupling_fail)
    show ?thesis using fs_header_coupling_read_bind[where k="?k a" and x=x, OF tail] False
      by (simp add: fs_throw_after)
  qed
  show ?case
    unfolding length_Cons replicate_Suc mmap.simps ro_alpha_round_def
      sm_bind_assoc sm_bind_return_left fs_header_guarded_alphas_Cons Let_def
    by (rule fs_header_coupling_bind[where xs="[]", simplified,
      OF fs_header_coupling_alpha_challenge]) (rule body[unfolded ro_alpha_round_def Let_def])
qed


lemma fs_header_staged_trace_slice:
  assumes select: "\<And>j cs. trace_fri_root_stage A j cs = return(roots!j)"
    and bound: "i+n \<le> length roots"
  shows "ro_staged_trace_fri_program A i n bs =
    (fs_header_write_fri receive_trace_fri_challenge (take n (drop i roots))
      \<bind> (\<lambda>cs. return(take n (drop i roots),bs@cs)))"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  show ?case by simp
next
  case (Suc n)
  have idx: "i<length roots" using Suc.prems by simp
  have tail: "Suc i+n\<le>length roots" using Suc.prems by simp
  have split: "take (Suc n) (drop i roots)=roots!i # take n(drop(Suc i)roots)"
    using Cons_nth_drop_Suc[OF idx] by (metis take_Suc_Cons)
  show ?case
    by (simp add: select split Suc.IH[OF tail] sm_bind_assoc)
qed

lemma fs_header_staged_composition_slice:
  assumes select: "\<And>j cs. composition_fri_root_stage A dg j cs = return(roots!j)"
    and bound: "i+n \<le> length roots"
  shows "ro_staged_composition_fri_program A dg i n bs =
    (fs_header_write_fri receive_composition_fri_challenge (take n (drop i roots))
      \<bind> (\<lambda>cs. return(take n (drop i roots),bs@cs)))"
  using bound
proof (induction n arbitrary: i bs)
  case 0
  show ?case by simp
next
  case (Suc n)
  have idx: "i<length roots" using Suc.prems by simp
  have tail: "Suc i+n\<le>length roots" using Suc.prems by simp
  have split: "take (Suc n) (drop i roots)=roots!i # take n(drop(Suc i)roots)"
    using Cons_nth_drop_Suc[OF idx] by (metis take_Suc_Cons)
  show ?case
    by (simp add: select split Suc.IH[OF tail] sm_bind_assoc)
qed

end
end
