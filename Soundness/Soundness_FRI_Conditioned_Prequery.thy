theory Soundness_FRI_Conditioned_Prequery
  imports
    Soundness_FRI_Prequery_Challenge_Bounds
    Soundness_FRI_Conditioned_Multiround
begin

context soundness
begin

lemma wp_receive_trace_fri_commits_actual_fresh_root_dependent_set:
  assumes local_bound: "\<And>r. card (B r) \<le> bd"
  shows
    "wp_event receive_trace_fri_commits
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((b, r), _) \<Rightarrow>
            b \<in> B r \<and>
            fmlookup (HashMap s)
              (TraceFriChallenge (PTraceFriCounter s)
                (concat (PState s) r)) = None) s
      \<le> nnreal bd / nnreal size"
  unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> (case None of None \<Rightarrow> False
      | Some ((b, r), _) \<Rightarrow>
          b \<in> B r \<and>
          fmlookup (HashMap s)
            (TraceFriChallenge (PTraceFriCounter s)
              (concat (PState s) r)) = None)"
    by simp
next
  fix r s_read
  assume read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
  have read_state: "PState s_read = concat (PState s) r"
    using read_outcome[OF read_r] by blast
  have read_counter: "PTraceFriCounter s_read = PTraceFriCounter s"
    using read_outcome[OF read_r] by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  let ?fresh =
    "fmlookup (HashMap s_read)
      (TraceFriChallenge (PTraceFriCounter s_read) (PState s_read)) = None"
  let ?Q =
    "\<lambda>out :: (('f \<times> 'f) \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some ((b, r'), _) \<Rightarrow>
          b \<in> B r' \<and>
          fmlookup (HashMap s)
            (TraceFriChallenge (PTraceFriCounter s)
              (concat (PState s) r')) = None"
  show "wp_event
      (receive_trace_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q s_read
      \<le> nnreal bd / nnreal size"
  proof (cases ?fresh)
    case True
    have fresh_key:
      "fmlookup (HashMap s)
        (TraceFriChallenge (PTraceFriCounter s) (concat (PState s) r)) =
        None"
      using True by (simp add: read_state read_counter read_hash)
    have cont_eq:
      "(\<lambda>out. case out of
          None \<Rightarrow> (0 :: prob)
        | Some (b, u) \<Rightarrow>
            wp (return (b, r)) (\<lambda>out. if ?Q out then 1 else 0) u) =
       (\<lambda>out :: ('f \<times> ('f, 'a) protocol_channel_scheme) option.
          if (case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> B r)
          then 1 else 0)"
      by (rule ext)
        (auto simp: wpsimps fresh_key split: option.splits prod.splits)
    have "wp_event
        (receive_trace_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q s_read =
        wp_event receive_trace_fri_challenge
          (\<lambda>out. case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> B r)
          s_read"
      unfolding wp_event_def by (simp add: wpsimps cont_eq)
    also have "... = nnreal (card (B r)) / nnreal size"
      by (rule wp_receive_trace_fri_challenge_fresh_set[OF True])
    also have "... \<le> nnreal bd / nnreal size"
      by (rule nnreal_nat_divide_right_mono[OF local_bound])
    finally show ?thesis .
  next
    case False
    have not_fresh_s:
      "fmlookup (HashMap s)
        (TraceFriChallenge (PTraceFriCounter s) (concat (PState s) r))
        \<noteq> None"
      using False by (simp add: read_state read_counter read_hash)
    have "wp_event
        (receive_trace_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q s_read
        \<le> wp_event
          (receive_trace_fri_challenge \<bind> (\<lambda>b. return (b, r)))
          (\<lambda>_ :: (('f \<times> 'f) \<times>
            ('f, 'a) protocol_channel_scheme) option. False) s_read"
      by (rule wp_event_mono_on_support)
        (use not_fresh_s in
          \<open>auto simp: wpsimps elim!: set_dist_bindE
            split: option.splits prod.splits\<close>)
    also have "... = 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
    also have "... \<le> nnreal bd / nnreal size"
      by simp
    finally show ?thesis .
  qed
qed



lemma wp_receive_composition_fri_commits_actual_fresh_root_dependent_set:
  assumes local_bound: "\<And>r. card (B r) \<le> bd"
  shows
    "wp_event receive_composition_fri_commits
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((b, r), _) \<Rightarrow>
            b \<in> B r \<and>
            fmlookup (HashMap s)
              (CompositionFriChallenge (PCompositionFriCounter s)
                (concat (PState s) r)) = None) s
      \<le> nnreal bd / nnreal size"
  unfolding receive_composition_fri_commits_def receive_fri_commits_with_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> (case None of None \<Rightarrow> False
      | Some ((b, r), _) \<Rightarrow>
          b \<in> B r \<and>
          fmlookup (HashMap s)
            (CompositionFriChallenge (PCompositionFriCounter s)
              (concat (PState s) r)) = None)"
    by simp
next
  fix r s_read
  assume read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
  have read_state: "PState s_read = concat (PState s) r"
    using read_outcome[OF read_r] by blast
  have read_counter: "PCompositionFriCounter s_read = PCompositionFriCounter s"
    using read_outcome[OF read_r] by blast
  have read_hash: "HashMap s_read = HashMap s"
    by (rule read_preserves_hash_map[OF read_r])
  let ?fresh =
    "fmlookup (HashMap s_read)
      (CompositionFriChallenge (PCompositionFriCounter s_read) (PState s_read)) = None"
  let ?Q =
    "\<lambda>out :: (('f \<times> 'f) \<times> ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some ((b, r'), _) \<Rightarrow>
          b \<in> B r' \<and>
          fmlookup (HashMap s)
            (CompositionFriChallenge (PCompositionFriCounter s)
              (concat (PState s) r')) = None"
  show "wp_event
      (receive_composition_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q s_read
      \<le> nnreal bd / nnreal size"
  proof (cases ?fresh)
    case True
    have fresh_key:
      "fmlookup (HashMap s)
        (CompositionFriChallenge (PCompositionFriCounter s) (concat (PState s) r)) =
        None"
      using True by (simp add: read_state read_counter read_hash)
    have cont_eq:
      "(\<lambda>out. case out of
          None \<Rightarrow> (0 :: prob)
        | Some (b, u) \<Rightarrow>
            wp (return (b, r)) (\<lambda>out. if ?Q out then 1 else 0) u) =
       (\<lambda>out :: ('f \<times> ('f, 'a) protocol_channel_scheme) option.
          if (case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> B r)
          then 1 else 0)"
      by (rule ext)
        (auto simp: wpsimps fresh_key split: option.splits prod.splits)
    have "wp_event
        (receive_composition_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q s_read =
        wp_event receive_composition_fri_challenge
          (\<lambda>out. case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> B r)
          s_read"
      unfolding wp_event_def by (simp add: wpsimps cont_eq)
    also have "... = nnreal (card (B r)) / nnreal size"
      by (rule wp_receive_composition_fri_challenge_fresh_set[OF True])
    also have "... \<le> nnreal bd / nnreal size"
      by (rule nnreal_nat_divide_right_mono[OF local_bound])
    finally show ?thesis .
  next
    case False
    have not_fresh_s:
      "fmlookup (HashMap s)
        (CompositionFriChallenge (PCompositionFriCounter s) (concat (PState s) r))
        \<noteq> None"
      using False by (simp add: read_state read_counter read_hash)
    have "wp_event
        (receive_composition_fri_challenge \<bind> (\<lambda>b. return (b, r))) ?Q s_read
        \<le> wp_event
          (receive_composition_fri_challenge \<bind> (\<lambda>b. return (b, r)))
          (\<lambda>_ :: (('f \<times> 'f) \<times>
            ('f, 'a) protocol_channel_scheme) option. False) s_read"
      by (rule wp_event_mono_on_support)
        (use not_fresh_s in
          \<open>auto simp: wpsimps elim!: set_dist_bindE
            split: option.splits prod.splits\<close>)
    also have "... = 0"
      unfolding wp_event_def wp_def dist_expect_def by simp
    also have "... \<le> nnreal bd / nnreal size"
      by simp
    finally show ?thesis .
  qed
qed

definition fri_online_conceptual_layer
  :: "nat \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list"
where
  "fri_online_conceptual_layer i s fri_root =
    conceptual_table s fri_root (length (fri_canonical_domain_at i))"

definition fri_online_bad_challenges
  :: "nat \<Rightarrow> nat \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f set"
where
  "fri_online_bad_challenges d i s fri_root =
    fri_conditioned_bad_challenges d
      (\<lambda>_ _. fri_online_conceptual_layer i s fri_root) i []"

lemma card_fri_online_bad_challenges_le_one:
  "card (fri_online_bad_challenges d i s fri_root) \<le> 1"
  unfolding fri_online_bad_challenges_def
  by (rule card_fri_conditioned_bad_challenges_le_one)

lemma wp_receive_trace_fri_commits_online_bad_fresh_bound:
  "wp_event receive_trace_fri_commits
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((b, fri_root), _) \<Rightarrow>
            b \<in> fri_online_bad_challenges d i s fri_root \<and>
            fmlookup (HashMap s)
              (TraceFriChallenge (PTraceFriCounter s)
                (concat (PState s) fri_root)) = None) s
    \<le> 1 / nnreal size"
proof -
  have bound:
      "wp_event receive_trace_fri_commits
        (\<lambda>out. case out of
            None \<Rightarrow> False
          | Some ((b, fri_root), _) \<Rightarrow>
              b \<in> fri_online_bad_challenges d i s fri_root \<and>
              fmlookup (HashMap s)
                (TraceFriChallenge (PTraceFriCounter s)
                  (concat (PState s) fri_root)) = None) s
      \<le> nnreal 1 / nnreal size"
    by (rule wp_receive_trace_fri_commits_actual_fresh_root_dependent_set)
      (rule card_fri_online_bad_challenges_le_one)
  show ?thesis
    using bound by simp
qed

lemma wp_receive_composition_fri_commits_online_bad_fresh_bound:
  "wp_event receive_composition_fri_commits
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some ((b, fri_root), _) \<Rightarrow>
            b \<in> fri_online_bad_challenges d i s fri_root \<and>
            fmlookup (HashMap s)
              (CompositionFriChallenge (PCompositionFriCounter s)
                (concat (PState s) fri_root)) = None) s
    \<le> 1 / nnreal size"
proof -
  have bound:
      "wp_event receive_composition_fri_commits
        (\<lambda>out. case out of
            None \<Rightarrow> False
          | Some ((b, fri_root), _) \<Rightarrow>
              b \<in> fri_online_bad_challenges d i s fri_root \<and>
              fmlookup (HashMap s)
                (CompositionFriChallenge (PCompositionFriCounter s)
                  (concat (PState s) fri_root)) = None) s
      \<le> nnreal 1 / nnreal size"
    by (rule wp_receive_composition_fri_commits_actual_fresh_root_dependent_set)
      (rule card_fri_online_bad_challenges_le_one)
  show ?thesis
    using bound by simp
qed

lemma hash_output_state:
  assumes outcome:
    "Some (hash_value, t) \<in> set_dist (execute (hash x) s)"
  shows "t = s\<lparr>HashMap := fmupd x hash_value (HashMap s)\<rparr>"
proof -
  from outcome obtain a s1 where
    a: "Some (a, s1) \<in> set_dist (execute (apply_hash x) s)"
    and rest: "Some (hash_value, t) \<in>
      set_dist (execute (modify_HashMap x a \<bind> (\<lambda>_. return a)) s1)"
  proof -
    have "Some (hash_value, t) \<in>
      set_dist (execute
        (apply_hash x \<bind>
          (\<lambda>a. modify_HashMap x a \<bind> (\<lambda>_. return a))) s)"
      using outcome unfolding hash_def .
    then show ?thesis
      by (rule set_dist_bindE) (rule that)
  qed
  have a_img:
      "Some (a, s1) \<in> (\<lambda>a. Some (a, s)) ` set_dist (hash_dist x s)"
    using a
    unfolding apply_hash_def lift.rep_eq lift_dist_def
    by (simp add: set_dist_dist_map)
  then have s1: "s1 = s"
    by auto
  from rest obtain unit_value s2 where
    mod:
      "Some (unit_value, s2) \<in>
        set_dist (execute (modify_HashMap x a) s1)"
    and ret:
      "Some (hash_value, t) \<in> set_dist (execute (return a) s2)"
    by (elim set_dist_bindE)
  have s2: "s2 = s1\<lparr>HashMap := fmupd x a (HashMap s1)\<rparr>"
    using mod unfolding modify_HashMap_def modify_def
    by (auto elim!: set_dist_bindE)
  have hash_value: "hash_value = a" and t: "t = s2"
    using ret by auto
  show ?thesis
    unfolding s1 s2 hash_value t by simp
qed

lemma protocol_receive_counted_tagged_output_state_unique:
  assumes out_t:
    "Some (b, t) \<in> set_dist
      (execute
        (protocol_receive_counted_tagged_random_field_element
          counter bump tag) s)"
    and out_u:
    "Some (b, u) \<in> set_dist
      (execute
        (protocol_receive_counted_tagged_random_field_element
          counter bump tag) s)"
  shows "t = u"
proof -
  from out_t obtain s0 hash_value ht mt where
    get_t: "Some (s0, s0) \<in> set_dist (execute get s)"
    and hash_t:
      "Some (hash_value, ht) \<in>
        set_dist (execute (hash (tag (counter s0) (PState s0))) s0)"
    and modify_t: "Some ((), mt) \<in> set_dist (execute (modify bump) ht)"
    and return_t:
      "Some (b, t) \<in> set_dist (execute (return hash_value) mt)"
    unfolding protocol_receive_counted_tagged_random_field_element_def
    by (auto elim!: set_dist_bindE)
  from out_u obtain s0' hash_value' hu mu where
    get_u: "Some (s0', s0') \<in> set_dist (execute get s)"
    and hash_u:
      "Some (hash_value', hu) \<in>
        set_dist (execute (hash (tag (counter s0') (PState s0'))) s0')"
    and modify_u: "Some ((), mu) \<in> set_dist (execute (modify bump) hu)"
    and return_u:
      "Some (b, u) \<in> set_dist (execute (return hash_value') mu)"
    unfolding protocol_receive_counted_tagged_random_field_element_def
    by (auto elim!: set_dist_bindE)
  have s0: "s0 = s" and s0': "s0' = s"
    using get_t get_u by auto
  have hash_value: "hash_value = b"
    and hash_value': "hash_value' = b"
    and t: "t = mt" and u: "u = mu"
    using return_t return_u by auto
  have ht0:
      "ht = s0\<lparr>HashMap :=
        fmupd (tag (counter s0) (PState s0)) hash_value (HashMap s0)\<rparr>"
    by (rule hash_output_state[OF hash_t])
  have ht:
      "ht = s\<lparr>HashMap :=
        fmupd (tag (counter s) (PState s)) b (HashMap s)\<rparr>"
    using ht0 unfolding s0 hash_value .
  have hu0:
      "hu = s0'\<lparr>HashMap :=
        fmupd (tag (counter s0') (PState s0')) hash_value' (HashMap s0')\<rparr>"
    by (rule hash_output_state[OF hash_u])
  have hu:
      "hu = s\<lparr>HashMap :=
        fmupd (tag (counter s) (PState s)) b (HashMap s)\<rparr>"
    using hu0 unfolding s0' hash_value' .
  have mt: "mt = bump ht"
    using modify_t unfolding modify_def
    by (auto elim!: set_dist_bindE)
  have mu: "mu = bump hu"
    using modify_u unfolding modify_def
    by (auto elim!: set_dist_bindE)
  show ?thesis
    unfolding t u mt mu ht hu by simp
qed

lemma receive_trace_fri_commits_output_state_unique:
  assumes out_t:
    "Some ((b, r), t) \<in> set_dist (execute receive_trace_fri_commits s)"
    and out_u:
    "Some ((b, r), u) \<in> set_dist (execute receive_trace_fri_commits s)"
  shows "t = u"
proof -
  from out_t obtain s_read where
    read_t: "Some (r, s_read) \<in> set_dist (execute read s)"
    and challenge_t:
      "Some (b, t) \<in> set_dist (execute receive_trace_fri_challenge s_read)"
    unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  from out_u obtain s_read' where
    read_u: "Some (r, s_read') \<in> set_dist (execute read s)"
    and challenge_u:
      "Some (b, u) \<in> set_dist (execute receive_trace_fri_challenge s_read')"
    unfolding receive_trace_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  obtain rest where transcript: "PTranscript s = r # rest"
    using receive_trace_fri_commits_outcome[OF out_t] by blast
  have read_t_exact:
      "s_read = s\<lparr>PState := concat (PState s) r,
        PTranscript := rest\<rparr>"
    using read_nonempty_outcome[OF read_t transcript] by simp
  have read_u_exact:
      "s_read' = s\<lparr>PState := concat (PState s) r,
        PTranscript := rest\<rparr>"
    using read_nonempty_outcome[OF read_u transcript] by simp
  have read_eq: "s_read' = s_read"
    using read_t_exact read_u_exact by simp
  have challenge_u_same:
      "Some (b, u) \<in>
        set_dist (execute receive_trace_fri_challenge s_read)"
    using challenge_u read_eq by simp
  show ?thesis
    unfolding receive_trace_fri_challenge_def
    by (rule protocol_receive_counted_tagged_output_state_unique[
          OF challenge_t[unfolded receive_trace_fri_challenge_def]
            challenge_u_same[unfolded receive_trace_fri_challenge_def]])
qed

fun trace_fri_online_bad_fresh_path
  :: "nat \<Rightarrow> nat \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<times> 'f) list \<Rightarrow> bool"
where
  "trace_fri_online_bad_fresh_path d i s [] = False"
| "trace_fri_online_bad_fresh_path d i s ((b, fri_root) # brs) =
    (b \<in> fri_online_bad_challenges d i s fri_root \<and>
       fmlookup (HashMap s)
         (TraceFriChallenge (PTraceFriCounter s)
           (concat (PState s) fri_root)) = None \<or>
     (\<exists>t. Some ((b, fri_root), t) \<in>
          set_dist (execute receive_trace_fri_commits s) \<and>
        trace_fri_online_bad_fresh_path d (Suc i) t brs))"

lemma trace_fri_online_bad_fresh_path_step:
  assumes head:
    "Some ((b, fri_root), t) \<in>
      set_dist (execute receive_trace_fri_commits s)"
  shows
    "trace_fri_online_bad_fresh_path d i s ((b, fri_root) # brs) \<longleftrightarrow>
      (b \<in> fri_online_bad_challenges d i s fri_root \<and>
         fmlookup (HashMap s)
           (TraceFriChallenge (PTraceFriCounter s)
             (concat (PState s) fri_root)) = None) \<or>
      trace_fri_online_bad_fresh_path d (Suc i) t brs"
  unfolding trace_fri_online_bad_fresh_path.simps
  by (metis receive_trace_fri_commits_output_state_unique head)
lemma wp_ntimes_receive_trace_fri_commits_online_bad_fresh_bound:
  "wp_event (ntimes receive_trace_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            trace_fri_online_bad_fresh_path d i s brs) s
    \<le> nnreal n / nnreal size"
proof (induction n arbitrary: s i)
  case 0
  then show ?case
    unfolding ntimes.simps wp_event_def wp_def dist_expect_def
      return.rep_eq dist_return_def
    by (simp add: dist_delta_dist delta_map_def)
next
  case (Suc n)
  let ?tail =
    "ntimes receive_trace_fri_commits n ::
      (('f \<times> 'f) list, ('f, 'a) protocol_channel_scheme) state_monad"
  let ?Q =
    "\<lambda>out :: ((('f \<times> 'f) list) \<times>
        ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow>
          trace_fri_online_bad_fresh_path d i s brs"
  let ?Head =
    "\<lambda>out :: (('f \<times> 'f) \<times>
        ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some ((b, fri_root), _) \<Rightarrow>
          b \<in> fri_online_bad_challenges d i s fri_root \<and>
          fmlookup (HashMap s)
            (TraceFriChallenge (PTraceFriCounter s)
              (concat (PState s) fri_root)) = None"
  let ?QHead =
    "\<lambda>out :: ((('f \<times> 'f) list) \<times>
        ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow>
          (case brs of
             [] \<Rightarrow> False
           | (b, fri_root) # _ \<Rightarrow>
               b \<in> fri_online_bad_challenges d i s fri_root \<and>
               fmlookup (HashMap s)
                 (TraceFriChallenge (PTraceFriCounter s)
                   (concat (PState s) fri_root)) = None)"
  let ?QTail =
    "\<lambda>out :: ((('f \<times> 'f) list) \<times>
        ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow>
          (case brs of
             [] \<Rightarrow> False
           | (b, fri_root) # brs' \<Rightarrow>
               \<exists>t. Some ((b, fri_root), t) \<in>
                    set_dist (execute receive_trace_fri_commits s) \<and>
                  trace_fri_online_bad_fresh_path d (Suc i) t brs')"
  have head_once:
      "wp_event receive_trace_fri_commits ?Head s \<le> 1 / nnreal size"
    by (rule wp_receive_trace_fri_commits_online_bad_fresh_bound)
  have head_bound:
      "wp_event (ntimes receive_trace_fri_commits (Suc n))
        ?QHead s \<le> 1 / nnreal size"
  proof -
    have
      "wp_event
        (receive_trace_fri_commits \<bind>
          (\<lambda>br. ?tail \<bind> (\<lambda>brs. return (br # brs))))
        ?QHead s \<le> 1 / nnreal size"
    proof (rule wp_event_bind_bound_by_head_event[OF head_once])
      show "?QHead None \<Longrightarrow> ?Head None"
        by simp
    next
      fix br t out
      assume head_out:
          "Some (br, t) \<in>
            set_dist (execute receive_trace_fri_commits s)"
        and cont_out:
          "out \<in> set_dist
            (execute (?tail \<bind> (\<lambda>brs. return (br # brs))) t)"
        and hit: "?QHead out"
      obtain b fri_root where br: "br = (b, fri_root)"
        by (cases br)
      show "?Head (Some (br, t))"
        using cont_out hit br
        by (auto elim!: set_dist_bindE split: option.splits prod.splits list.splits)
    qed
    then show ?thesis
      by simp
  qed
  have tail_bound:
      "wp_event (ntimes receive_trace_fri_commits (Suc n))
        ?QTail s \<le> nnreal n / nnreal size"
  proof -
    have
      "wp_event
        (receive_trace_fri_commits \<bind>
          (\<lambda>br. ?tail \<bind> (\<lambda>brs. return (br # brs))))
        ?QTail s \<le> nnreal n / nnreal size"
    proof (rule wp_event_bind_bound_by_cont)
      show "\<not> ?QTail None"
        by simp
    next
      fix br t
      assume head_out:
        "Some (br, t) \<in> set_dist (execute receive_trace_fri_commits s)"
      obtain b fri_root where br: "br = (b, fri_root)"
        by (cases br)
      let ?TailP =
        "\<lambda>out :: ((('f \<times> 'f) list) \<times>
            ('f, 'a) protocol_channel_scheme) option.
          case out of
            None \<Rightarrow> False
          | Some (brs, _) \<Rightarrow>
              trace_fri_online_bad_fresh_path d (Suc i) t brs"
      have tail_ih:
          "wp_event ?tail ?TailP t \<le> nnreal n / nnreal size"
        by (rule Suc.IH)
      show
        "wp_event (?tail \<bind> (\<lambda>brs. return (br # brs)))
          ?QTail t \<le> nnreal n / nnreal size"
      proof (rule order_trans[OF wp_event_bind_bound_by_head_event[
            OF tail_ih]])
        show "?QTail None \<Longrightarrow> ?TailP None"
          by simp
      next
        fix brs u out
        assume tail_out:
            "Some (brs, u) \<in> set_dist (execute ?tail t)"
          and return_out:
            "out \<in> set_dist (execute (return (br # brs)) u)"
          and hit: "?QTail out"
        have out_eq: "out = Some (br # brs, u)"
          using return_out
          unfolding set_dist_def return.rep_eq dist_return_def
            dist_delta_dist delta_map_def by simp
        from hit obtain t' where
          head_out':
            "Some ((b, fri_root), t') \<in>
              set_dist (execute receive_trace_fri_commits s)"
          and tail_hit:
            "trace_fri_online_bad_fresh_path d (Suc i) t' brs"
          unfolding out_eq br by auto
        have t'_eq: "t' = t"
          by (rule receive_trace_fri_commits_output_state_unique[
              OF head_out' head_out[unfolded br]])
        show "?TailP (Some (brs, u))"
          using tail_hit t'_eq by simp
      next
        show "nnreal n / nnreal size \<le> nnreal n / nnreal size"
          by simp
      qed
    qed
    then show ?thesis
      by simp
  qed
  have split:
      "wp_event (ntimes receive_trace_fri_commits (Suc n)) ?Q s \<le>
        wp_event (ntimes receive_trace_fri_commits (Suc n))
          (\<lambda>out. ?QHead out \<or> ?QTail out) s"
    by (rule wp_event_mono)
      (auto split: option.splits prod.splits list.splits)
  also have "... \<le>
      wp_event (ntimes receive_trace_fri_commits (Suc n)) ?QHead s +
      wp_event (ntimes receive_trace_fri_commits (Suc n)) ?QTail s"
    by (rule wp_event_union_bound)
  also have "... \<le> 1 / nnreal size + nnreal n / nnreal size"
    by (rule add_mono[OF head_bound tail_bound])
  also have "... = nnreal (Suc n) / nnreal size"
    using size_card by transfer (simp add: field_simps)
  finally show ?case .
qed

lemma receive_composition_fri_commits_output_state_unique:
  assumes out_t:
    "Some ((b, r), t) \<in> set_dist (execute receive_composition_fri_commits s)"
    and out_u:
    "Some ((b, r), u) \<in> set_dist (execute receive_composition_fri_commits s)"
  shows "t = u"
proof -
  from out_t obtain s_read where
    read_t: "Some (r, s_read) \<in> set_dist (execute read s)"
    and challenge_t:
      "Some (b, t) \<in> set_dist (execute receive_composition_fri_challenge s_read)"
    unfolding receive_composition_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  from out_u obtain s_read' where
    read_u: "Some (r, s_read') \<in> set_dist (execute read s)"
    and challenge_u:
      "Some (b, u) \<in> set_dist (execute receive_composition_fri_challenge s_read')"
    unfolding receive_composition_fri_commits_def receive_fri_commits_with_def
    by (auto elim!: set_dist_bindE)
  obtain rest where transcript: "PTranscript s = r # rest"
    using receive_composition_fri_commits_outcome[OF out_t] by blast
  have read_t_exact:
      "s_read = s\<lparr>PState := concat (PState s) r,
        PTranscript := rest\<rparr>"
    using read_nonempty_outcome[OF read_t transcript] by simp
  have read_u_exact:
      "s_read' = s\<lparr>PState := concat (PState s) r,
        PTranscript := rest\<rparr>"
    using read_nonempty_outcome[OF read_u transcript] by simp
  have read_eq: "s_read' = s_read"
    using read_t_exact read_u_exact by simp
  have challenge_u_same:
      "Some (b, u) \<in>
        set_dist (execute receive_composition_fri_challenge s_read)"
    using challenge_u read_eq by simp
  show ?thesis
    unfolding receive_composition_fri_challenge_def
    by (rule protocol_receive_counted_tagged_output_state_unique[
          OF challenge_t[unfolded receive_composition_fri_challenge_def]
            challenge_u_same[unfolded receive_composition_fri_challenge_def]])
qed

fun composition_fri_online_bad_fresh_path
  :: "nat \<Rightarrow> nat \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<times> 'f) list \<Rightarrow> bool"
where
  "composition_fri_online_bad_fresh_path d i s [] = False"
| "composition_fri_online_bad_fresh_path d i s ((b, fri_root) # brs) =
    (b \<in> fri_online_bad_challenges d i s fri_root \<and>
       fmlookup (HashMap s)
         (CompositionFriChallenge (PCompositionFriCounter s)
           (concat (PState s) fri_root)) = None \<or>
     (\<exists>t. Some ((b, fri_root), t) \<in>
          set_dist (execute receive_composition_fri_commits s) \<and>
        composition_fri_online_bad_fresh_path d (Suc i) t brs))"

lemma composition_fri_online_bad_fresh_path_step:
  assumes head:
    "Some ((b, fri_root), t) \<in>
      set_dist (execute receive_composition_fri_commits s)"
  shows
    "composition_fri_online_bad_fresh_path d i s ((b, fri_root) # brs) \<longleftrightarrow>
      (b \<in> fri_online_bad_challenges d i s fri_root \<and>
         fmlookup (HashMap s)
           (CompositionFriChallenge (PCompositionFriCounter s)
             (concat (PState s) fri_root)) = None) \<or>
      composition_fri_online_bad_fresh_path d (Suc i) t brs"
  unfolding composition_fri_online_bad_fresh_path.simps
  by (metis receive_composition_fri_commits_output_state_unique head)
lemma wp_ntimes_receive_composition_fri_commits_online_bad_fresh_bound:
  "wp_event (ntimes receive_composition_fri_commits n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (brs, _) \<Rightarrow>
            composition_fri_online_bad_fresh_path d i s brs) s
    \<le> nnreal n / nnreal size"
proof (induction n arbitrary: s i)
  case 0
  then show ?case
    by (simp add: wp_event_def wpsimps)
next
  case (Suc n)
  let ?tail =
    "ntimes receive_composition_fri_commits n ::
      (('f \<times> 'f) list, ('f, 'a) protocol_channel_scheme) state_monad"
  let ?Q =
    "\<lambda>out :: ((('f \<times> 'f) list) \<times>
        ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow>
          composition_fri_online_bad_fresh_path d i s brs"
  let ?Head =
    "\<lambda>out :: (('f \<times> 'f) \<times>
        ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some ((b, fri_root), _) \<Rightarrow>
          b \<in> fri_online_bad_challenges d i s fri_root \<and>
          fmlookup (HashMap s)
            (CompositionFriChallenge (PCompositionFriCounter s)
              (concat (PState s) fri_root)) = None"
  let ?QHead =
    "\<lambda>out :: ((('f \<times> 'f) list) \<times>
        ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow>
          (case brs of
             [] \<Rightarrow> False
           | (b, fri_root) # _ \<Rightarrow>
               b \<in> fri_online_bad_challenges d i s fri_root \<and>
               fmlookup (HashMap s)
                 (CompositionFriChallenge (PCompositionFriCounter s)
                   (concat (PState s) fri_root)) = None)"
  let ?QTail =
    "\<lambda>out :: ((('f \<times> 'f) list) \<times>
        ('f, 'a) protocol_channel_scheme) option.
      case out of
        None \<Rightarrow> False
      | Some (brs, _) \<Rightarrow>
          (case brs of
             [] \<Rightarrow> False
           | (b, fri_root) # brs' \<Rightarrow>
               \<exists>t. Some ((b, fri_root), t) \<in>
                    set_dist (execute receive_composition_fri_commits s) \<and>
                  composition_fri_online_bad_fresh_path d (Suc i) t brs')"
  have head_once:
      "wp_event receive_composition_fri_commits ?Head s \<le> 1 / nnreal size"
    by (rule wp_receive_composition_fri_commits_online_bad_fresh_bound)
  have head_bound:
      "wp_event (ntimes receive_composition_fri_commits (Suc n))
        ?QHead s \<le> 1 / nnreal size"
  proof -
    have
      "wp_event
        (receive_composition_fri_commits \<bind>
          (\<lambda>br. ?tail \<bind> (\<lambda>brs. return (br # brs))))
        ?QHead s \<le> 1 / nnreal size"
    proof (rule wp_event_bind_bound_by_head_event[OF head_once])
      show "?QHead None \<Longrightarrow> ?Head None"
        by simp
    next
      fix br t out
      assume head_out:
          "Some (br, t) \<in>
            set_dist (execute receive_composition_fri_commits s)"
        and cont_out:
          "out \<in> set_dist
            (execute (?tail \<bind> (\<lambda>brs. return (br # brs))) t)"
        and hit: "?QHead out"
      obtain b fri_root where br: "br = (b, fri_root)"
        by (cases br)
      show "?Head (Some (br, t))"
        using cont_out hit br
        by (auto elim!: set_dist_bindE split: option.splits prod.splits list.splits)
    qed
    then show ?thesis
      by simp
  qed
  have tail_bound:
      "wp_event (ntimes receive_composition_fri_commits (Suc n))
        ?QTail s \<le> nnreal n / nnreal size"
  proof -
    have
      "wp_event
        (receive_composition_fri_commits \<bind>
          (\<lambda>br. ?tail \<bind> (\<lambda>brs. return (br # brs))))
        ?QTail s \<le> nnreal n / nnreal size"
    proof (rule wp_event_bind_bound_by_cont)
      show "\<not> ?QTail None"
        by simp
    next
      fix br t
      assume head_out:
        "Some (br, t) \<in> set_dist (execute receive_composition_fri_commits s)"
      obtain b fri_root where br: "br = (b, fri_root)"
        by (cases br)
      let ?TailP =
        "\<lambda>out :: ((('f \<times> 'f) list) \<times>
            ('f, 'a) protocol_channel_scheme) option.
          case out of
            None \<Rightarrow> False
          | Some (brs, _) \<Rightarrow>
              composition_fri_online_bad_fresh_path d (Suc i) t brs"
      have tail_ih:
          "wp_event ?tail ?TailP t \<le> nnreal n / nnreal size"
        by (rule Suc.IH)
      show
        "wp_event (?tail \<bind> (\<lambda>brs. return (br # brs)))
          ?QTail t \<le> nnreal n / nnreal size"
      proof (rule order_trans[OF wp_event_bind_bound_by_head_event[
            OF tail_ih]])
        show "?QTail None \<Longrightarrow> ?TailP None"
          by simp
      next
        fix brs u out
        assume tail_out:
            "Some (brs, u) \<in> set_dist (execute ?tail t)"
          and return_out:
            "out \<in> set_dist (execute (return (br # brs)) u)"
          and hit: "?QTail out"
        have out_eq: "out = Some (br # brs, u)"
          using return_out
          unfolding set_dist_def return.rep_eq dist_return_def
            dist_delta_dist delta_map_def by simp
        from hit obtain t' where
          head_out':
            "Some ((b, fri_root), t') \<in>
              set_dist (execute receive_composition_fri_commits s)"
          and tail_hit:
            "composition_fri_online_bad_fresh_path d (Suc i) t' brs"
          unfolding out_eq br by auto
        have t'_eq: "t' = t"
          by (rule receive_composition_fri_commits_output_state_unique[
              OF head_out' head_out[unfolded br]])
        show "?TailP (Some (brs, u))"
          using tail_hit t'_eq by simp
      next
        show "nnreal n / nnreal size \<le> nnreal n / nnreal size"
          by simp
      qed
    qed
    then show ?thesis
      by simp
  qed
  have split:
      "wp_event (ntimes receive_composition_fri_commits (Suc n)) ?Q s \<le>
        wp_event (ntimes receive_composition_fri_commits (Suc n))
          (\<lambda>out. ?QHead out \<or> ?QTail out) s"
    by (rule wp_event_mono)
      (auto split: option.splits prod.splits list.splits)
  also have "... \<le>
      wp_event (ntimes receive_composition_fri_commits (Suc n)) ?QHead s +
      wp_event (ntimes receive_composition_fri_commits (Suc n)) ?QTail s"
    by (rule wp_event_union_bound)
  also have "... \<le> 1 / nnreal size + nnreal n / nnreal size"
    by (rule add_mono[OF head_bound tail_bound])
  also have "... = nnreal (Suc n) / nnreal size"
    using size_card by transfer (simp add: field_simps)
  finally show ?case .
qed

end

end
