(* Title: Stark/Soundness_FRI_Weighted_Verifier_Logging.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Verifier_Logging
  imports
    "Soundness_FRI_Weighted_Staged_Logging"
begin

section \<open>Verifier Logging for weighted MCA soundness\<close>

text \<open>Derive the verifier logger from actual authentication and FRI operations and combine it with the staged adversary program under the existing full-experiment hash budget.\<close>

subsection \<open>Logged Verifier Primitives\<close>

context soundness
begin

lemmas lc_program_modify_preserves_hash_map = lc_program_modify

lemma lc_program_ntimes:
  fixes m :: "('x, 'f protocol_channel) state_monad"
  assumes m: "lc_program n m"
  shows "lc_program (k * n) (ntimes m k)"
  using m
proof (induction k)
  case 0
  then show ?case
    by (simp add: lc_program_return)
next
  case (Suc k)
  have tail: "lc_program (k * n) (ntimes m k)"
    using Suc.IH Suc.prems by simp
  have cont:
    "lc_program (k * n + 0)
      (ntimes m k \<bind> (\<lambda>xs. return (x # xs)))" for x
    by (rule lc_program_bind[OF tail lc_program_return])
  have "lc_program (n + (k * n + 0))
      (m \<bind> (\<lambda>x. ntimes m k \<bind> (\<lambda>xs. return (x # xs))))"
    by (rule lc_program_bind[OF Suc.prems cont])
  then show ?case
    by simp
qed

lemma lc_program_mmap:
  fixes ms :: "('x, 'f protocol_channel) state_monad list"
  assumes ms: "\<And>m. m \<in> set ms \<Longrightarrow> lc_program n m"
  shows "lc_program (length ms * n) (mmap ms)"
  using ms
proof (induction ms)
  case Nil
  then show ?case
    by (simp add: lc_program_return)
next
  case (Cons m ms)
  have head: "lc_program n m"
    using Cons.prems by simp
  have tail: "lc_program (length ms * n) (mmap ms)"
    using Cons.IH Cons.prems by simp
  have cont:
    "lc_program (length ms * n + 0)
      (mmap ms \<bind> (\<lambda>xs. return (x # xs)))" for x
    by (rule lc_program_bind[OF tail lc_program_return])
  have "lc_program (n + (length ms * n + 0))
      (m \<bind> (\<lambda>x. mmap ms \<bind> (\<lambda>xs. return (x # xs))))"
    by (rule lc_program_bind[OF head cont])
  then show ?case
    by simp
qed

lemma lc_program_protocol_absorb_read:
  "lc_program 1
    (protocol_absorb_read :: ('f, 'f, unit) protocol_c_monad)"
proof -
  have get_step:
    "lc_program 0
      (get :: ('f protocol_channel,
        'f protocol_channel) state_monad)"
    by (rule lc_program_get)
  have modify_then_return:
    "lc_program (0 + 0)
      (modify
        (\<lambda>t. t\<lparr>PState := h,
          PTranscript := tl (PTranscript t)\<rparr>) \<bind>
        (\<lambda>_. return (hd (PTranscript s))) ::
        ('f, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel" and h :: 'f
    by (rule lc_program_bind)
      (rule lc_program_modify_preserves_hash_map, simp,
       rule lc_program_return)
  have hash_then_tail:
    "lc_program (1 + (0 + 0))
      (hash (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
        (\<lambda>h. modify
          (\<lambda>t. t\<lparr>PState := h,
            PTranscript := tl (PTranscript t)\<rparr>) \<bind>
          (\<lambda>_. return (hd (PTranscript s)))) ::
        ('f, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel"
    by (rule lc_program_bind)
      (rule lc_program_hash, rule modify_then_return)
  have assert_then_tail:
    "lc_program (0 + (1 + (0 + 0)))
      (assert (PTranscript s \<noteq> []) \<bind>
        (\<lambda>_. hash
          (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
          (\<lambda>h. modify
            (\<lambda>t. t\<lparr>PState := h,
              PTranscript := tl (PTranscript t)\<rparr>) \<bind>
            (\<lambda>_. return (hd (PTranscript s))))) ::
        ('f, 'f protocol_channel) state_monad)"
    for s :: "'f protocol_channel"
    by (rule lc_program_bind)
      (rule lc_program_assert, rule hash_then_tail)
  have "lc_program (0 + (0 + (1 + (0 + 0))))
      (get \<bind>
        (\<lambda>s :: 'f protocol_channel.
          assert (PTranscript s \<noteq> []) \<bind>
            (\<lambda>_. hash
              (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
              (\<lambda>h. modify
                (\<lambda>t. t\<lparr>PState := h,
                  PTranscript := tl (PTranscript t)\<rparr>) \<bind>
                (\<lambda>_. return (hd (PTranscript s)))))))"
    by (rule lc_program_bind[OF get_step assert_then_tail])
  then show ?thesis
    unfolding protocol_absorb_read_def
    by simp
qed

lemma lc_program_protocol_check_authentication_path_raw:
  fixes leaf :: "'f protocol_hash_input"
  shows "lc_program (Suc (length path))
    (protocol_merkle.check_authentication_path len i leaf path ::
      ('f, 'f protocol_channel) state_monad)"
proof (induction path arbitrary: len i)
  case Nil
  have hash_budget:
    "lc_program 1
      (hash leaf :: ('f, 'f protocol_channel) state_monad)"
    by (rule lc_program_hash)
  then show ?case
    by simp
next
  case (Cons a path)
  show ?case
  proof (cases "i < len div 2")
    case True
    have rec:
      "lc_program (Suc (length path))
        (protocol_merkle.check_authentication_path (len div 2) i leaf path ::
          ('f, 'f protocol_channel) state_monad)"
      using Cons.IH[of "len div 2" i] by simp
    have bound:
      "lc_program (Suc (length path) + 1)
        ((protocol_merkle.check_authentication_path (len div 2) i leaf path ::
            ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>x. hash (MerkleNode x a)))"
      by (rule lc_program_bind[OF rec lc_program_hash])
    show ?thesis
      using True bound
      by simp
  next
    case False
    have rec:
      "lc_program (Suc (length path))
        (protocol_merkle.check_authentication_path
          (len div 2) (i - len div 2) leaf path ::
          ('f, 'f protocol_channel) state_monad)"
      using Cons.IH[of "len div 2" "i - len div 2"] by simp
    have bound:
      "lc_program (Suc (length path) + 1)
        ((protocol_merkle.check_authentication_path
          (len div 2) (i - len div 2) leaf path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>x. hash (MerkleNode a x)))"
      by (rule lc_program_bind[OF rec lc_program_hash])
    show ?thesis
      using False bound
      by simp
  qed
qed

lemma lc_program_check_authentication_path:
  "lc_program (Suc (length path))
    (check_authentication_path len i v path)"
  unfolding check_authentication_path_def protocol_check_authentication_path_def
  by (rule lc_program_protocol_check_authentication_path_raw)

lemma lc_program_ntimes_protocol_absorb_read_bind:
  fixes k :: "'f list \<Rightarrow> ('y, 'f protocol_channel) state_monad"
  assumes k: "\<And>xs. length xs = n \<Longrightarrow> lc_program b (k xs)"
  shows "lc_program (n + b)
    ((ntimes protocol_absorb_read n :: ('f list, 'f protocol_channel) state_monad) \<bind> k)"
proof -
  have reads:
    "lc_program (n * 1)
      (ntimes protocol_absorb_read n ::
        ('f list, 'f protocol_channel) state_monad)"
    by (rule lc_program_ntimes)
      (rule lc_program_protocol_absorb_read)
  have "lc_program (n * 1 + b)
      ((ntimes protocol_absorb_read n ::
        ('f list, 'f protocol_channel) state_monad) \<bind> k)"
  proof (rule lc_program_bind_on_outcomes[OF reads])
    fix s xs t
    assume out:
      "Some (xs, t) \<in>
        set_dist (execute
          (ntimes protocol_absorb_read n ::
            ('f list, 'f protocol_channel) state_monad) s)"
    show "lc_program b (k xs)"
      by (rule k) (rule ntimes_outcome_length[OF out])
  qed
  then show ?thesis by simp
qed

lemma lc_program_check_authentication_path_assert_return:
  fixes path :: "'f list"
    and v root :: "'f"
    and r :: "'r"
  shows
  "lc_program (Suc (length path))
    (((check_authentication_path len i v path ::
        ('f, 'f protocol_channel) state_monad) \<bind>
      (\<lambda>ap. assert (ap = root) \<bind> (\<lambda>_. return r))))"
proof -
  have check_budget:
    "lc_program (Suc (length path))
      (check_authentication_path len i v path ::
        ('f, 'f protocol_channel) state_monad)"
    by (rule lc_program_check_authentication_path)
  have assert_return:
    "lc_program (0 + 0)
      (assert (ap = root) \<bind> (\<lambda>_. return r) ::
        ('r, 'f protocol_channel) state_monad)" for ap
    by (rule lc_program_bind
        [OF lc_program_assert lc_program_return])
  have "lc_program (Suc (length path) + (0 + 0))
      (((check_authentication_path len i v path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = root) \<bind> (\<lambda>_. return r))))"
    by (rule lc_program_bind[OF check_budget assert_return])
  then show ?thesis by simp
qed

lemma lc_program_check_authentication_path_assert_bind:
  fixes path :: "'f list"
    and v root :: "'f"
    and k :: "unit \<Rightarrow> ('r, 'f protocol_channel) state_monad"
  assumes k: "\<And>u. lc_program n (k u)"
  shows
  "lc_program (Suc (length path) + n)
    (((check_authentication_path len i v path ::
        ('f, 'f protocol_channel) state_monad) \<bind>
      (\<lambda>ap. assert (ap = root) \<bind> k)))"
proof -
  have check_budget:
    "lc_program (Suc (length path))
      (check_authentication_path len i v path ::
        ('f, 'f protocol_channel) state_monad)"
    by (rule lc_program_check_authentication_path)
  have assert_cont:
    "lc_program (0 + n)
      (assert (ap = root) \<bind> k ::
        ('r, 'f protocol_channel) state_monad)" for ap
    by (rule lc_program_bind[OF lc_program_assert k])
  have "lc_program (Suc (length path) + (0 + n))
    (((check_authentication_path len i v path ::
        ('f, 'f protocol_channel) state_monad) \<bind>
      (\<lambda>ap. assert (ap = root) \<bind> k)))"
    by (rule lc_program_bind[OF check_budget assert_cont])
  then show ?thesis by simp
qed

lemma lc_program_fri_layer_opening_finish:
  assumes xp_path_len: "length xp_path = floor_log len"
    and xn_path_len: "length xn_path = floor_log len"
  shows
    "lc_program (Suc (floor_log len) + Suc (floor_log len))
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
proof -
  let ?b = "Suc (floor_log len)"
  let ?sidx = "(i + len div 2) mod len"
  let ?out =
    "(i mod (len div 2),
      (xp + xn) div 2 +
        b * ((xp - xn) div (2 * ((h ^ i) * shift) ^ pw)),
      len div 2, pw + pw)"
  have second:
    "lc_program ?b
      (((check_authentication_path len ?sidx xn xn_path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))"
    by (subst xn_path_len[symmetric])
      (rule lc_program_check_authentication_path_assert_return)
  have second_cont:
    "\<And>u. lc_program ?b
      (((check_authentication_path len ?sidx xn xn_path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))"
    using second by simp
  have first0:
    "lc_program (Suc (length xp_path) + ?b)
      (((check_authentication_path len i xp xp_path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind>
          (\<lambda>_.
            (check_authentication_path len ?sidx xn xn_path ::
              ('f, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    by (rule lc_program_check_authentication_path_assert_bind
        [OF second_cont])
  have first:
    "lc_program (?b + ?b)
      (((check_authentication_path len i xp xp_path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind>
          (\<lambda>_.
            (check_authentication_path len ?sidx xn xn_path ::
              ('f, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    using first0 xp_path_len by simp
  have raw:
    "lc_program (0 + (?b + ?b))
      ((assert (xp = x) ::
          (unit, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>_.
          (check_authentication_path len i xp xp_path ::
            ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = f) \<bind>
            (\<lambda>_.
              (check_authentication_path len ?sidx xn xn_path ::
                ('f, 'f protocol_channel) state_monad) \<bind>
              (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    by (rule lc_program_bind[OF lc_program_assert first])
  have all:
    "lc_program (?b + ?b)
      ((assert (xp = x) ::
          (unit, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>_.
          (check_authentication_path len i xp xp_path ::
            ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = f) \<bind>
            (\<lambda>_.
              (check_authentication_path len ?sidx xn xn_path ::
                ('f, 'f protocol_channel) state_monad) \<bind>
              (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    using raw by simp
  from all show ?thesis
    unfolding fri_layer_opening_finish_def
    by (simp add: Let_def)
qed

lemma lc_program_ro_query_decommitment_step:
  "lc_program (2 * Suc (floor_log (scale * clength)))
    (ro_query_decommitment_step fr i)"
proof -
  let ?len = "scale * clength"
  let ?L = "floor_log ?len"
  have path_tail:
    "lc_program (Suc ?L)
      ((check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
    if path_len: "length path = ?L" for qh path
  proof -
    have exact:
      "lc_program (Suc (length path))
        ((check_authentication_path ?len i qh path ::
            ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (rule lc_program_check_authentication_path_assert_return)
    then show ?thesis
      using path_len by simp
  qed
  have after_path:
    "lc_program (?L + Suc ?L)
      ((ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))" for qh
    by (rule lc_program_ntimes_protocol_absorb_read_bind)
      (rule path_tail)
  have whole:
    "lc_program (1 + (?L + Suc ?L))
      (protocol_absorb_read \<bind>
        (\<lambda>qh. (ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))) ::
        ('f, 'f protocol_channel) state_monad)"
    by (rule lc_program_bind)
      (rule lc_program_protocol_absorb_read, rule after_path)
  have budget_eq: "1 + (?L + Suc ?L) = 2 * Suc ?L"
    by simp
  have whole':
    "lc_program (2 * Suc ?L)
      (protocol_absorb_read \<bind>
        (\<lambda>qh. (ntimes protocol_absorb_read ?L ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>path. (check_authentication_path ?len i qh path ::
          ('f, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))) ::
        ('f, 'f protocol_channel) state_monad)"
    using whole unfolding budget_eq .
  show ?thesis
    using whole' unfolding ro_query_decommitment_step_def
    by (simp add: Let_def mult.commute)

qed

lemma lc_program_ro_check_decommit_on_query:
  "lc_program ro_verifier_query_decommit_hash_budget
    (mmap (ro_check_decommit_on_query fr idx))"
proof -
  let ?b = "2 * Suc (floor_log (scale * clength))"
  let ?steps =
    "map (ro_query_decommitment_step fr) (powers_scaled idx)"
  have step_budget:
    "\<And>m. m \<in> set ?steps \<Longrightarrow> lc_program ?b m"
  proof -
    fix m
    assume "m \<in> set ?steps"
    then obtain j where m_eq: "m = ro_query_decommitment_step fr j"
      by auto
    show "lc_program ?b m"
      unfolding m_eq by (rule lc_program_ro_query_decommitment_step)
  qed
  have map_budget:
    "lc_program (length ?steps * ?b) (mmap ?steps)"
    by (rule lc_program_mmap) (rule step_budget)
  then show ?thesis
    unfolding ro_check_decommit_on_query_def
      ro_verifier_query_decommit_hash_budget_def
      verifier_query_decommit_hash_budget_def powers_scaled_def
    by (simp add: algebra_simps)
qed

lemma lc_program_ro_fri_layer_opening_step:
  assumes len_le: "floor_log len \<le> L"
  shows "lc_program (2 * (Suc L + Suc L))
    (ro_fri_layer_opening_step (b, f) (i, x, len, pw))"
proof -
  let ?l = "floor_log len"
  let ?exact = "Suc ?l + Suc ?l"
  have finish:
    "lc_program ?exact
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
    if xp_len: "length xp_path = ?l"
      and xn_len: "length xn_path = ?l"
    for xp xp_path xn xn_path
    by (rule lc_program_fri_layer_opening_finish
        [OF xp_len xn_len])
  have after_xn_path:
    "lc_program (?l + ?exact)
      ((ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
          xp xp_path xn xn_path))"
    if xp_len: "length xp_path = ?l" for xp xp_path xn
    by (rule lc_program_ntimes_protocol_absorb_read_bind)
      (rule finish[OF xp_len])
  have after_xn:
    "lc_program (1 + (?l + ?exact))
      (protocol_absorb_read \<bind>
        (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
            xp xp_path xn xn_path)) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    if xp_len: "length xp_path = ?l" for xp xp_path
    by (rule lc_program_bind)
      (rule lc_program_protocol_absorb_read,
        rule after_xn_path[OF xp_len])
  have after_xp_path:
    "lc_program (?l + (1 + (?l + ?exact)))
      ((ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>xp_path. protocol_absorb_read \<bind>
          (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
            ('f list, 'f protocol_channel) state_monad) \<bind>
            (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
              xp xp_path xn xn_path))) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)" for xp
    by (rule lc_program_ntimes_protocol_absorb_read_bind)
      (rule after_xn)
  have whole:
    "lc_program (1 + (?l + (1 + (?l + ?exact))))
      (protocol_absorb_read \<bind>
        (\<lambda>xp. (ntimes protocol_absorb_read ?l ::
          ('f list, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>xp_path. protocol_absorb_read \<bind>
            (\<lambda>xn. (ntimes protocol_absorb_read ?l ::
              ('f list, 'f protocol_channel) state_monad) \<bind>
              (\<lambda>xn_path. fri_layer_opening_finish b f i x len pw
                xp xp_path xn xn_path)))) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    by (rule lc_program_bind)
      (rule lc_program_protocol_absorb_read, rule after_xp_path)
  have budget_eq:
    "1 + (?l + (1 + (?l + ?exact))) = 2 * ?exact"
    by simp
  have exact:
    "lc_program (2 * ?exact)
      (ro_fri_layer_opening_step (b, f) (i, x, len, pw))"
    using whole unfolding ro_fri_layer_opening_step_def budget_eq
    by simp
  have le: "2 * ?exact \<le> 2 * (Suc L + Suc L)"
    using len_le by simp
  show ?thesis
    by (rule lc_program_mono[OF le exact])
qed

end

subsection \<open>Logged Verifier Program\<close>

context soundness
begin

lemma lc_program_ro_fri_layer_opening_steps_mfold_state:
  fixes st :: "nat \<times> 'f \<times> nat \<times> nat"
  assumes init:
    "case st of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
  shows
    "lc_program
      (length fl * (2 * (Suc L + Suc L)))
      (mfold st (map ro_fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
  using init
proof (induction fl arbitrary: st)
  case Nil
  then show ?case
    by (simp add: lc_program_return)
next
  case (Cons bf fl)
  obtain i x len pw where st_eq: "st = (i, x, len, pw)"
    by (cases st)
  obtain b f where bf_eq: "bf = (b, f)"
    by (cases bf)
  let ?B = "2 * (Suc L + Suc L)"
  have len_le: "floor_log len \<le> L"
    using Cons.prems unfolding st_eq by simp
  have head:
    "lc_program ?B
      (ro_fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    unfolding bf_eq st_eq
    by (rule lc_program_ro_fri_layer_opening_step[OF len_le])
  have tail:
    "lc_program (length fl * ?B)
      (mfold z (map ro_fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    if out:
      "Some (z, t) \<in>
        set_dist (execute (ro_fri_layer_opening_step bf st) s)"
    for z and s :: "'f protocol_channel"
      and t :: "'f protocol_channel"
  proof -
    have z_inv:
      "case z of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
      unfolding bf_eq st_eq
      by (rule ro_fri_layer_opening_step_preserves_floor_log_bound[OF len_le out[unfolded bf_eq st_eq]])
    show ?thesis
      by (rule Cons.IH[OF z_inv])
  qed
  have "lc_program (?B + length fl * ?B)
      ((ro_fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>z. mfold z (map ro_fri_layer_opening_step fl)))"
    by (rule lc_program_bind_on_outcomes[OF head]) (rule tail)
  then show ?case
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma lc_program_ro_receive_query_commits_mfold:
  assumes init: "floor_log len \<le> L"
  shows
    "lc_program
      (length fl * (2 * (Suc L + Suc L)))
      (mfold (i, x, len, pw) (ro_receive_query_commits fl))"
  unfolding ro_receive_query_commits_eq_fri_layer_opening_steps
proof -
  have st_inv:
    "case (i, x, len, pw) of
      (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
    using init by simp
  show "lc_program (length fl * (2 * (Suc L + Suc L)))
    (mfold (i, x, len, pw) (map ro_fri_layer_opening_step fl) ::
      (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
    by (rule lc_program_ro_fri_layer_opening_steps_mfold_state
        [OF st_inv])
qed

lemma lc_program_ro_verifier_query_round_program_exact:
  "lc_program
    (1 + ro_verifier_query_decommit_hash_budget +
      (length f_fl + length fl) * ro_verifier_fri_layer_hash_budget)
    (ro_verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?L = "floor_log (clength * scale)"
  let ?B = "ro_verifier_fri_layer_hash_budget"
  have B_eq: "?B = 2 * (Suc ?L + Suc ?L)"
    unfolding ro_verifier_fri_layer_hash_budget_def
      verifier_fri_layer_hash_budget_def by simp
  have after_comp:
    "lc_program (length fl * ?B + 0)
      ((mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (ro_receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad) \<bind>
        (\<lambda>(i, x, len, pw). assert (x = final)))"
    for idx fv
  proof (rule lc_program_bind)
    show "lc_program (length fl * ?B)
      (mfold
        (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
        (ro_receive_query_commits fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule lc_program_ro_receive_query_commits_mfold) simp
    show "\<And>x. lc_program 0
      ((case x of (i, x, len, pw) \<Rightarrow> assert (x = final)) ::
        (unit, 'f protocol_channel) state_monad)"
      by (simp add: lc_program_assert split: prod.splits)
  qed
  have after_trace:
    "lc_program
      (length f_fl * ?B + (0 + (length fl * ?B + 0)))
      ((mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
          'f protocol_channel) state_monad) \<bind>
        (\<lambda>(f_i, f_x, f_len, f_pow).
          assert (f_x = f_final) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final)))))"
    for idx fv
  proof (rule lc_program_bind)
    show "lc_program (length f_fl * ?B)
      (mfold (idx, hd fv, clength * scale, 1)
        (ro_receive_query_commits f_fl) ::
        (nat \<times> 'f \<times> nat \<times> nat, 'f protocol_channel) state_monad)"
      unfolding B_eq
      by (rule lc_program_ro_receive_query_commits_mfold) simp
    fix x :: "nat \<times> 'f \<times> nat \<times> nat"
    obtain f_i f_x f_len f_pow where x_eq:
      "x = (f_i, f_x, f_len, f_pow)"
      by (cases x) auto
    have case_budget:
      "lc_program (0 + (length fl * ?B + 0))
        ((assert (f_x = f_final) ::
          (unit, 'f protocol_channel) state_monad) \<bind>
          (\<lambda>_. (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (ro_receive_query_commits fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(i, x, len, pw). assert (x = final))))"
      by (rule lc_program_bind
          [OF lc_program_assert after_comp])
    show "lc_program (0 + (length fl * ?B + 0))
      ((case x of (f_i, f_x, f_len, f_pow) \<Rightarrow>
        assert (f_x = f_final) \<bind>
        (\<lambda>_. (mfold
          (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
          (ro_receive_query_commits fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(i, x, len, pw). assert (x = final)))) ::
        (unit, 'f protocol_channel) state_monad)"
      using case_budget
      unfolding x_eq
      by (simp split: prod.splits)
  qed
  have after_query:
    "lc_program
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + (0 + (length fl * ?B + 0))))
      (mmap (ro_check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (ro_receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                'f protocol_channel) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    by (rule lc_program_bind)
      (rule lc_program_ro_check_decommit_on_query, rule after_trace)
  have after_query_simple:
    "lc_program
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      (mmap (ro_check_decommit_on_query fr idx) \<bind>
        (\<lambda>fv. (mfold (idx, hd fv, clength * scale, 1)
          (ro_receive_query_commits f_fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            'f protocol_channel) state_monad) \<bind>
          (\<lambda>(f_i, f_x, f_len, f_pow).
            assert (f_x = f_final) \<bind>
            (\<lambda>_. (mfold
              (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
              (ro_receive_query_commits fl) ::
              (nat \<times> 'f \<times> nat \<times> nat,
                'f protocol_channel) state_monad) \<bind>
              (\<lambda>(i, x, len, pw). assert (x = final))))))"
    for idx
    using after_query[of idx] by simp
  have after_random:
    "lc_program
      (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B))
      ((let idx' = index (to_nat idx) in
          mmap (ro_check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (ro_receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  'f protocol_channel) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    for idx
    using after_query_simple[of "index (to_nat idx)"]
    by (simp add: Let_def algebra_simps split: prod.splits)
  have "lc_program
      (1 + (ro_verifier_query_decommit_hash_budget +
        (length f_fl * ?B + length fl * ?B)))
      (receive_query_index_challenge \<bind>
        (\<lambda>idx.
          let idx' = index (to_nat idx) in
          mmap (ro_check_decommit_on_query fr idx') \<bind>
          (\<lambda>fv. (mfold (idx', hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl) ::
            (nat \<times> 'f \<times> nat \<times> nat,
              'f protocol_channel) state_monad) \<bind>
            (\<lambda>(f_i, f_x, f_len, f_pow).
              assert (f_x = f_final) \<bind>
              (\<lambda>_. (mfold
                (idx', cp_eval as fv (h ^ idx' * shift), clength * scale, 1)
                (ro_receive_query_commits fl) ::
                (nat \<times> 'f \<times> nat \<times> nat,
                  'f protocol_channel) state_monad) \<bind>
                (\<lambda>(i, x, len, pw). assert (x = final)))))))"
    by (rule lc_program_bind
        [OF lc_program_receive_query_index_challenge])
      (rule after_random)
  then show ?thesis
    unfolding ro_verifier_query_round_program_def
    by (simp add: Let_def algebra_simps split: prod.splits)
qed

lemma lc_program_ro_verifier_query_round_program:
  assumes trace_len: "length f_fl \<le> ceil_log clength"
    and comp_len: "length fl \<le> ceil_log (maxDegree + 1)"
  shows "lc_program ro_verifier_query_round_hash_budget
    (ro_verifier_query_round_program fr f_fl f_final as fl final)"
proof -
  let ?exact = "1 + ro_verifier_query_decommit_hash_budget +
    (length f_fl + length fl) * ro_verifier_fri_layer_hash_budget"
  have exact:
    "lc_program ?exact
      (ro_verifier_query_round_program fr f_fl f_final as fl final)"
    by (rule lc_program_ro_verifier_query_round_program_exact)
  have len_le:
    "length f_fl + length fl \<le> ceil_log clength + ceil_log (maxDegree + 1)"
    using trace_len comp_len by simp
  have le: "?exact \<le> ro_verifier_query_round_hash_budget"
    unfolding ro_verifier_query_round_hash_budget_def
    using mult_right_mono[OF len_le, of ro_verifier_fri_layer_hash_budget]
    by simp
  show ?thesis
    by (rule lc_program_mono[OF le exact])
qed

lemma lc_program_ro_receive_fri_commits_with:
  assumes challenge: "lc_program q receive_challenge"
  shows "lc_program (1 + q)
    (ro_receive_fri_commits_with receive_challenge)"
proof -
  have cont:
    "\<And>r. lc_program (q + 0)
      (receive_challenge \<bind> (\<lambda>b. return (b, r)))"
    by (rule lc_program_bind)
      (rule challenge, rule lc_program_return)
  have budget:
    "lc_program (1 + (q + 0))
      (ro_receive_fri_commits_with receive_challenge)"
    unfolding ro_receive_fri_commits_with_def
    by (rule lc_program_bind)
      (rule lc_program_protocol_absorb_read, rule cont)
  then show ?thesis by simp
qed

lemma lc_program_ro_receive_trace_fri_commits:
  "lc_program (1 + 1) ro_receive_trace_fri_commits"
  using lc_program_ro_receive_fri_commits_with
    [OF lc_program_receive_trace_fri_challenge]
  unfolding ro_receive_trace_fri_commits_def by simp

lemma lc_program_ro_receive_composition_fri_commits:
  "lc_program (1 + 1) ro_receive_composition_fri_commits"
  using lc_program_ro_receive_fri_commits_with
    [OF lc_program_receive_composition_fri_challenge]
  unfolding ro_receive_composition_fri_commits_def by simp

lemma lc_program_ro_alpha_round:
  "lc_program (1 + 1) ro_alpha_round"
proof -
  have assert_return:
    "lc_program (0 + 0)
      (assert (a0 = a1) \<bind> (\<lambda>_. return a1) ::
        ('f, 'f protocol_channel) state_monad)" for a0 a1
    by (rule lc_program_bind)
      (rule lc_program_assert, rule lc_program_return)
  have after_absorb:
    "lc_program (1 + (0 + 0))
      (protocol_absorb_read \<bind>
        (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1)) ::
        ('f, 'f protocol_channel) state_monad)" for a0
    by (rule lc_program_bind)
      (rule lc_program_protocol_absorb_read, rule assert_return)
  have whole:
    "lc_program (1 + (1 + (0 + 0)))
      (receive_alpha_challenge \<bind>
        (\<lambda>a0. protocol_absorb_read \<bind>
          (\<lambda>a1. assert (a0 = a1) \<bind> (\<lambda>_. return a1))) ::
        ('f, 'f protocol_channel) state_monad)"
    by (rule lc_program_bind)
      (rule lc_program_receive_alpha_challenge, rule after_absorb)
  then show ?thesis
    unfolding ro_alpha_round_def by simp
qed

lemma lc_program_ntimes_ro_receive_trace_fri_commits_bound:
  assumes "n \<le> N"
  shows "lc_program (N * (1 + 1))
    (ntimes ro_receive_trace_fri_commits n)"
proof -
  have exact: "lc_program (n * (1 + 1))
    (ntimes ro_receive_trace_fri_commits n)"
    by (rule lc_program_ntimes)
      (rule lc_program_ro_receive_trace_fri_commits)
  have le: "n * (1 + 1) \<le> N * (1 + 1)"
    using assms by (simp add: mult_right_mono)
  show ?thesis by (rule lc_program_mono[OF le exact])
qed

lemma lc_program_ntimes_ro_receive_composition_fri_commits_bound:
  assumes "n \<le> N"
  shows "lc_program (N * (1 + 1))
    (ntimes ro_receive_composition_fri_commits n)"
proof -
  have exact: "lc_program (n * (1 + 1))
    (ntimes ro_receive_composition_fri_commits n)"
    by (rule lc_program_ntimes)
      (rule lc_program_ro_receive_composition_fri_commits)
  have le: "n * (1 + 1) \<le> N * (1 + 1)"
    using assms by (simp add: mult_right_mono)
  show ?thesis by (rule lc_program_mono[OF le exact])
qed

lemma lc_program_ro_verify_monad:
  "lc_program ro_verifier_hash_query_budget ro_verify_monad"
proof -
  let ?Q = "rounds * ro_verifier_query_round_hash_budget"
  have alpha_map:
    "lc_program (length spec * (1 + 1))
      (mmap (replicate (length spec) ro_alpha_round))"
  proof -
    let ?steps = "replicate (length spec) ro_alpha_round"
    have step_budget:
      "\<And>m. m \<in> set ?steps \<Longrightarrow> lc_program (1 + 1) m"
    proof -
      fix m
      assume "m \<in> set ?steps"
      then have "m = ro_alpha_round"
        by simp
      then show "lc_program (1 + 1) m"
        by (simp only: add_Suc_right add_0 lc_program_ro_alpha_round)
    qed
    have "lc_program (length ?steps * (1 + 1)) (mmap ?steps)"
      by (rule lc_program_mmap) (rule step_budget)
    then show ?thesis by simp
  qed
  have after_final:
    "lc_program (1 + ?Q)
      (protocol_absorb_read \<bind>
        (\<lambda>final. ntimes
          (ro_verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
    for fr f_fl f_final as fl
    by (rule lc_program_bind)
      (rule lc_program_protocol_absorb_read,
       rule lc_program_ntimes,
       rule lc_program_ro_verifier_query_round_program
        [OF len_f len_fl])
  have after_comp_fri:
    "lc_program
      (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))
      ((ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
        (\<lambda>fl. protocol_absorb_read \<bind>
          (\<lambda>final. ntimes
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
    if len_f: "length f_fl \<le> ceil_log clength"
      and dg_bound: "to_nat dg \<le> maxDegree"
    for fr f_fl f_final as dg
  proof (rule lc_program_bind_on_outcomes)
    show "lc_program (ceil_log (maxDegree + 1) * (1 + 1))
      (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
        ((('f \<times> 'f) list), 'f protocol_channel) state_monad)"
      by (rule lc_program_ntimes_ro_receive_composition_fri_commits_bound)
        (rule ceil_log_to_nat_degree_bound[OF dg_bound])
    fix s fl t
    assume out:
      "Some (fl, t) \<in>
        set_dist (execute
          (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list), 'f protocol_channel) state_monad) s)"
    have len_fl: "length fl \<le> ceil_log (maxDegree + 1)"
      using ntimes_outcome_length[OF out]
        ceil_log_to_nat_degree_bound[OF dg_bound]
      by simp
    show "lc_program (1 + ?Q)
      (protocol_absorb_read \<bind>
        (\<lambda>final. ntimes
          (ro_verifier_query_round_program fr f_fl f_final as fl final)
          rounds))"
      by (rule after_final[OF len_f len_fl])
  qed
  have after_degree_assert:
    "lc_program
      (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q)))
      (assert (to_nat dg \<le> maxDegree) \<bind>
        (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
          (\<lambda>fl. protocol_absorb_read \<bind>
            (\<lambda>final. ntimes
              (ro_verifier_query_round_program fr f_fl f_final as fl final)
              rounds))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as dg
  proof (rule lc_program_bind_on_outcomes)
    show "lc_program 0
      (assert (to_nat dg \<le> maxDegree) ::
        (unit, 'f protocol_channel) state_monad)"
      by (rule lc_program_assert)
    fix s u t
    assume out:
      "Some (u, t) \<in>
        set_dist (execute
          (assert (to_nat dg \<le> maxDegree) ::
            (unit, 'f protocol_channel) state_monad) s)"
    have dg_bound: "to_nat dg \<le> maxDegree"
      using out unfolding assert_def
      by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
    show "lc_program
      (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))
      ((ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
        (\<lambda>fl. protocol_absorb_read \<bind>
          (\<lambda>final. ntimes
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            rounds)))"
      by (rule after_comp_fri[OF len_f dg_bound])
  qed
  have after_dg:
    "lc_program
      (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))))
      (protocol_absorb_read \<bind>
        (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
          (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
            ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
            (\<lambda>fl. protocol_absorb_read \<bind>
              (\<lambda>final. ntimes
                (ro_verifier_query_round_program fr f_fl f_final as fl final)
                rounds)))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final as
    by (rule lc_program_bind)
      (rule lc_program_protocol_absorb_read,
       rule after_degree_assert[OF len_f])
  have after_alpha:
    "lc_program
      (length spec * (1 + 1) +
        (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q)))))
      (mmap (replicate (length spec) ro_alpha_round) \<bind>
        (\<lambda>as. protocol_absorb_read \<bind>
          (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
            (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
              ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
              (\<lambda>fl. protocol_absorb_read \<bind>
                (\<lambda>final. ntimes
                  (ro_verifier_query_round_program fr f_fl f_final as fl final)
                  rounds))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl f_final
    by (rule lc_program_bind)
      (rule alpha_map, rule after_dg[OF len_f])
  have after_f_final:
    "lc_program
      (1 + (length spec * (1 + 1) +
        (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))))))
      (protocol_absorb_read \<bind>
        (\<lambda>f_final. mmap (replicate (length spec) ro_alpha_round) \<bind>
          (\<lambda>as. protocol_absorb_read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
                (\<lambda>fl. protocol_absorb_read \<bind>
                  (\<lambda>final. ntimes
                    (ro_verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
    if len_f: "length f_fl \<le> ceil_log clength"
    for fr f_fl
    by (rule lc_program_bind)
      (rule lc_program_protocol_absorb_read,
       rule after_alpha[OF len_f])
  have after_trace_fri:
    "lc_program
      (ceil_log clength * (1 + 1) +
        (1 + (length spec * (1 + 1) +
          (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q)))))))
      ((ntimes ro_receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
        (\<lambda>f_fl. protocol_absorb_read \<bind>
          (\<lambda>f_final. mmap (replicate (length spec) ro_alpha_round) \<bind>
            (\<lambda>as. protocol_absorb_read \<bind>
              (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                  ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
                  (\<lambda>fl. protocol_absorb_read \<bind>
                    (\<lambda>final. ntimes
                      (ro_verifier_query_round_program fr f_fl f_final as fl final)
                      rounds))))))))"
    for fr
  proof (rule lc_program_bind_on_outcomes)
    show "lc_program (ceil_log clength * (1 + 1))
      (ntimes ro_receive_trace_fri_commits (ceil_log clength) ::
        ((('f \<times> 'f) list), 'f protocol_channel) state_monad)"
      by (rule lc_program_ntimes_ro_receive_trace_fri_commits_bound) simp
    fix s f_fl t
    assume out:
      "Some (f_fl, t) \<in>
        set_dist (execute
          (ntimes ro_receive_trace_fri_commits (ceil_log clength) ::
            ((('f \<times> 'f) list), 'f protocol_channel) state_monad) s)"
    have len_f: "length f_fl \<le> ceil_log clength"
      using ntimes_outcome_length[OF out] by simp
    show "lc_program
      (1 + (length spec * (1 + 1) +
        (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))))))
      (protocol_absorb_read \<bind>
        (\<lambda>f_final. mmap (replicate (length spec) ro_alpha_round) \<bind>
          (\<lambda>as. protocol_absorb_read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
                (\<lambda>fl. protocol_absorb_read \<bind>
                  (\<lambda>final. ntimes
                    (ro_verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)))))))"
      by (rule after_f_final[OF len_f])
  qed
  have top:
    "lc_program
      (1 + (ceil_log clength * (1 + 1) +
        (1 + (length spec * (1 + 1) +
          (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q))))))))
      (protocol_absorb_read \<bind>
        (\<lambda>fr. (ntimes ro_receive_trace_fri_commits (ceil_log clength) ::
          ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
          (\<lambda>f_fl. protocol_absorb_read \<bind>
            (\<lambda>f_final. mmap (replicate (length spec) ro_alpha_round) \<bind>
              (\<lambda>as. protocol_absorb_read \<bind>
                (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
                  (\<lambda>_. (ntimes ro_receive_composition_fri_commits (ceil_log (to_nat dg + 1)) ::
                    ((('f \<times> 'f) list), 'f protocol_channel) state_monad) \<bind>
                    (\<lambda>fl. protocol_absorb_read \<bind>
                      (\<lambda>final. ntimes
                        (ro_verifier_query_round_program fr f_fl f_final as fl final)
                        rounds)))))))))"
    by (rule lc_program_bind)
      (rule lc_program_protocol_absorb_read,
       rule after_trace_fri)
  let ?top_budget =
    "1 + (ceil_log clength * (1 + 1) +
      (1 + (length spec * (1 + 1) +
        (1 + (0 + (ceil_log (maxDegree + 1) * (1 + 1) + (1 + ?Q)))))))"
  have top': "lc_program ?top_budget ro_verify_monad"
    using top
    unfolding ro_verify_monad_def
    by simp
  have budget_eq: "?top_budget = ro_verifier_hash_query_budget"
    unfolding ro_verifier_hash_query_budget_def
      ro_verifier_header_hash_budget_def verifier_header_hash_budget_def
    by (simp add: algebra_simps)
  show ?thesis
    using top' budget_eq by simp
qed

lemma lc_program_verifier_state_transfer:
 "lc_program 0 (verifier_state_transfer tr)"
 by (rule lc_preserving) (rule hash_map_preserving_verifier_state_transfer)

lemma lc_program_ro_checked_verifier_state_transfer_with_saved:
 "lc_program 0 (ro_checked_verifier_state_transfer_with_saved tr)"
 by (rule lc_preserving) (rule hash_map_preserving_ro_checked_verifier_state_transfer_with_saved)

lemma lc_program_ro_verifier_after_adversary:
  "lc_program ro_verifier_hash_query_budget
    (verifier_state_transfer tr \<bind> (\<lambda>_. ro_verify_monad))"
proof -
  have "lc_program (0 + ro_verifier_hash_query_budget)
    (verifier_state_transfer tr \<bind> (\<lambda>_. ro_verify_monad))"
    by (rule lc_program_bind)
      (rule lc_program_verifier_state_transfer,
       rule lc_program_ro_verify_monad)
  then show ?thesis by simp
qed

lemma lc_program_ro_absorb_checked_staged_security_experiment:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "lc_program
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      (ro_absorb_checked_staged_security_experiment A)"
proof -
  have cont:
    "\<And>data. lc_program ro_verifier_hash_query_budget
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. ro_verify_monad)))"
    using lc_program_ro_verifier_after_adversary
      [of "staged_proof_transcript data" for data]
    unfolding verifier_state_transfer_def sm_bind_assoc .
  have budget:
    "lc_program
      (ro_checked_staged_transcript_hash_query_budget_for budgets +
        ro_verifier_hash_query_budget)
      (ro_absorb_checked_staged_security_experiment A)"
    unfolding ro_absorb_checked_staged_security_experiment_def
    by (rule lc_program_bind)
      (rule lc_program_ro_checked_staged_transcript_program
        [OF wf controlled], rule cont)
  then show ?thesis
    unfolding ro_absorb_checked_staged_security_hash_query_budget_for_def .
qed

lemma lc_program_ro_absorb_checked_staged_security_experiment_with_data_state:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "lc_program
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      (ro_absorb_checked_staged_security_experiment_with_data_state A)"
proof -
  let ?head = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have verify_return_range:
    "\<And>data saved. lc_program (ro_verifier_hash_query_budget + 0)
      (ro_verify_monad \<bind>
        (\<lambda>result. return ((data, saved), result)))"
    by (rule lc_program_bind)
      (rule lc_program_ro_verify_monad, rule lc_program_return)
  have cont_range:
    "\<And>data. lc_program (0 + (ro_verifier_hash_query_budget + 0))
      (ro_checked_verifier_state_transfer_with_saved
          (staged_proof_transcript data) \<bind>
        (\<lambda>saved. ro_verify_monad \<bind>
          (\<lambda>result. return ((data, saved), result))))"
    by (rule lc_program_bind)
      (rule lc_program_ro_checked_verifier_state_transfer_with_saved,
        rule verify_return_range)
  have whole:
    "lc_program
      (?head + (0 + (ro_verifier_hash_query_budget + 0)))
      (ro_checked_staged_transcript_program A \<bind>
        (\<lambda>data.
          ro_checked_verifier_state_transfer_with_saved
            (staged_proof_transcript data) \<bind>
          (\<lambda>saved. ro_verify_monad \<bind>
            (\<lambda>result. return ((data, saved), result)))))"
    by (rule lc_program_bind)
      (rule
        lc_program_ro_checked_staged_transcript_program[OF wf controlled],
        rule cont_range)
  show ?thesis
    using whole
    unfolding ro_absorb_checked_staged_security_experiment_with_data_state_def
      ro_checked_verifier_state_transfer_with_saved_def
      ro_absorb_checked_staged_security_hash_query_budget_for_def
    by (simp add: sm_bind_assoc add.assoc)
qed

end

end
