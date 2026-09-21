theory Soundness_FRI_Conditioned_RO_Prequery
  imports
    Stark.Soundness_FRI_Conditioned_Prequery
    Stark.Staged_Security_Experiment_RO_Checked
begin

context soundness
begin

definition ro_receive_trace_fri_commits_with_prefix
  :: "(((('f protocol_channel \<times> 'f protocol_channel) \<times> ('f \<times> 'f))),
      'f protocol_channel) state_monad"
where
  "ro_receive_trace_fri_commits_with_prefix = do {
     before \<leftarrow> get;
     fri_root \<leftarrow> protocol_absorb_read;
     root_state \<leftarrow> get;
     b \<leftarrow> receive_trace_fri_challenge;
     return ((before, root_state), (b, fri_root))
   }"

definition ro_receive_composition_fri_commits_with_prefix
  :: "(((('f protocol_channel \<times> 'f protocol_channel) \<times> ('f \<times> 'f))),
      'f protocol_channel) state_monad"
where
  "ro_receive_composition_fri_commits_with_prefix = do {
     before \<leftarrow> get;
     fri_root \<leftarrow> protocol_absorb_read;
     root_state \<leftarrow> get;
     b \<leftarrow> receive_composition_fri_challenge;
     return ((before, root_state), (b, fri_root))
   }"

definition ro_trace_fri_online_bad_fresh_item
where
  "ro_trace_fri_online_bad_fresh_item d i item \<longleftrightarrow>
    (case item of ((before, root_state), (b, fri_root)) \<Rightarrow>
       b \<in> fri_online_bad_challenges d i root_state fri_root \<and>
       fmlookup (HashMap root_state)
         (TraceFriChallenge (PTraceFriCounter root_state)
           (PState root_state)) = None)"

definition ro_composition_fri_online_bad_fresh_item
where
  "ro_composition_fri_online_bad_fresh_item d i item \<longleftrightarrow>
    (case item of ((before, root_state), (b, fri_root)) \<Rightarrow>
       b \<in> fri_online_bad_challenges d i root_state fri_root \<and>
       fmlookup (HashMap root_state)
         (CompositionFriChallenge (PCompositionFriCounter root_state)
           (PState root_state)) = None)"

lemma wp_ro_receive_trace_fri_commits_with_prefix_online_bad_fresh_bound:
  "wp_event ro_receive_trace_fri_commits_with_prefix
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (item, _) \<Rightarrow> ro_trace_fri_online_bad_fresh_item d i item) s
    \<le> 1 / nnreal size"
  unfolding ro_receive_trace_fri_commits_with_prefix_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> (case None of
      None \<Rightarrow> False
    | Some (item, _) \<Rightarrow> ro_trace_fri_online_bad_fresh_item d i item)"
    by simp
next
  fix before s_before
  assume before_out: "Some (before, s_before) \<in> set_dist (execute get s)"
  have before_eq: "before = s" and s_before_eq: "s_before = s"
    using before_out by auto
  show
    "wp_event
      (protocol_absorb_read \<bind>
        (\<lambda>fri_root. get \<bind>
          (\<lambda>root_state. receive_trace_fri_challenge \<bind>
            (\<lambda>b. return ((before, root_state), (b, fri_root))))))
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (item, _) \<Rightarrow> ro_trace_fri_online_bad_fresh_item d i item)
      s_before
    \<le> 1 / nnreal size"
  unfolding before_eq s_before_eq
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> (case None of
        None \<Rightarrow> False
      | Some (item, _) \<Rightarrow> ro_trace_fri_online_bad_fresh_item d i item)"
      by simp
  next
    fix fri_root root_state
    assume root_out:
      "Some (fri_root, root_state) \<in>
        set_dist (execute protocol_absorb_read s)"
    let ?B = "fri_online_bad_challenges d i root_state fri_root"
    let ?Q =
      "\<lambda>out :: ((((('f protocol_channel \<times> 'f protocol_channel) \<times>
          ('f \<times> 'f))) \<times> 'f protocol_channel) option).
        case out of
          None \<Rightarrow> False
        | Some (item, _) \<Rightarrow> ro_trace_fri_online_bad_fresh_item d i item"
    let ?I = "\<lambda>out. if ?Q out then 1 else 0"
    have get_event_eq:
      "wp_event
        (get \<bind>
          (\<lambda>root_state. receive_trace_fri_challenge \<bind>
            (\<lambda>b. return ((s, root_state), (b, fri_root)))))
        ?Q root_state =
       wp_event
        (receive_trace_fri_challenge \<bind>
          (\<lambda>b. return ((s, root_state), (b, fri_root))))
        ?Q root_state"
      unfolding wp_event_def
      by (simp add: wpsimps)
    have challenge_bound:
      "wp_event
        (receive_trace_fri_challenge \<bind>
          (\<lambda>b. return ((s, root_state), (b, fri_root))))
        ?Q root_state
      \<le> 1 / nnreal size"
    proof (cases
        "fmlookup (HashMap root_state)
          (TraceFriChallenge (PTraceFriCounter root_state)
            (PState root_state)) = None")
      case True
      have event_eq:
        "wp_event
          (receive_trace_fri_challenge \<bind>
            (\<lambda>b. return ((s, root_state), (b, fri_root))))
          ?Q root_state =
         wp_event receive_trace_fri_challenge
          (\<lambda>out. case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> ?B)
          root_state"
        unfolding wp_event_def
        apply (simp only: wp_bind)
        apply (rule arg_cong[
          where f = "\<lambda>R. wp receive_trace_fri_challenge R root_state"])
        apply (rule ext)
        apply (case_tac r)
         apply simp
        apply (rename_tac out)
        apply (case_tac out)
        by (simp add: wpsimps
          ro_trace_fri_online_bad_fresh_item_def True)
      have "wp_event
          (receive_trace_fri_challenge \<bind>
            (\<lambda>b. return ((s, root_state), (b, fri_root))))
          ?Q root_state =
        nnreal (card ?B) / nnreal size"
        unfolding event_eq
        by (rule wp_receive_trace_fri_challenge_fresh_set[OF True])
      also have "... \<le> nnreal 1 / nnreal size"
        by (rule nnreal_nat_divide_right_mono)
          (rule card_fri_online_bad_challenges_le_one)
      also have "... = 1 / nnreal size"
        by simp
      finally show ?thesis .
    next
      case False
      have cont_zero:
        "(\<lambda>r. case r of
            None \<Rightarrow> ?I None
          | Some (b, st) \<Rightarrow>
              wp (return ((s, root_state), (b, fri_root))) ?I st)
         = (\<lambda>_. 0)"
        apply (rule ext)
        apply (case_tac r)
         apply simp
        apply (rename_tac out)
        apply (case_tac out)
        by (simp add: wpsimps
          ro_trace_fri_online_bad_fresh_item_def False)
      have event_false:
        "wp_event
          (receive_trace_fri_challenge \<bind>
            (\<lambda>b. return ((s, root_state), (b, fri_root))))
          ?Q root_state = 0"
        unfolding wp_event_def
        apply (simp only: wp_bind cont_zero)
        unfolding wp_def dist_expect_def
        by simp
      show ?thesis
        unfolding event_false by simp
    qed
    show
      "wp_event
        (get \<bind>
          (\<lambda>root_state. receive_trace_fri_challenge \<bind>
            (\<lambda>b. return ((s, root_state), (b, fri_root)))))
        ?Q root_state
      \<le> 1 / nnreal size"
      unfolding get_event_eq
      by (rule challenge_bound)
  qed
qed

lemma wp_ro_receive_composition_fri_commits_with_prefix_online_bad_fresh_bound:
  "wp_event ro_receive_composition_fri_commits_with_prefix
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (item, _) \<Rightarrow> ro_composition_fri_online_bad_fresh_item d i item) s
    \<le> 1 / nnreal size"
  unfolding ro_receive_composition_fri_commits_with_prefix_def
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> (case None of
      None \<Rightarrow> False
    | Some (item, _) \<Rightarrow> ro_composition_fri_online_bad_fresh_item d i item)"
    by simp
next
  fix before s_before
  assume before_out: "Some (before, s_before) \<in> set_dist (execute get s)"
  have before_eq: "before = s" and s_before_eq: "s_before = s"
    using before_out by auto
  show
    "wp_event
      (protocol_absorb_read \<bind>
        (\<lambda>fri_root. get \<bind>
          (\<lambda>root_state. receive_composition_fri_challenge \<bind>
            (\<lambda>b. return ((before, root_state), (b, fri_root))))))
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (item, _) \<Rightarrow> ro_composition_fri_online_bad_fresh_item d i item)
      s_before
    \<le> 1 / nnreal size"
  unfolding before_eq s_before_eq
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> (case None of
        None \<Rightarrow> False
      | Some (item, _) \<Rightarrow> ro_composition_fri_online_bad_fresh_item d i item)"
      by simp
  next
    fix fri_root root_state
    assume root_out:
      "Some (fri_root, root_state) \<in>
        set_dist (execute protocol_absorb_read s)"
    let ?B = "fri_online_bad_challenges d i root_state fri_root"
    let ?Q =
      "\<lambda>out :: ((((('f protocol_channel \<times> 'f protocol_channel) \<times>
          ('f \<times> 'f))) \<times> 'f protocol_channel) option).
        case out of
          None \<Rightarrow> False
        | Some (item, _) \<Rightarrow> ro_composition_fri_online_bad_fresh_item d i item"
    let ?I = "\<lambda>out. if ?Q out then 1 else 0"
    have get_event_eq:
      "wp_event
        (get \<bind>
          (\<lambda>root_state. receive_composition_fri_challenge \<bind>
            (\<lambda>b. return ((s, root_state), (b, fri_root)))))
        ?Q root_state =
       wp_event
        (receive_composition_fri_challenge \<bind>
          (\<lambda>b. return ((s, root_state), (b, fri_root))))
        ?Q root_state"
      unfolding wp_event_def
      by (simp add: wpsimps)
    have challenge_bound:
      "wp_event
        (receive_composition_fri_challenge \<bind>
          (\<lambda>b. return ((s, root_state), (b, fri_root))))
        ?Q root_state
      \<le> 1 / nnreal size"
    proof (cases
        "fmlookup (HashMap root_state)
          (CompositionFriChallenge (PCompositionFriCounter root_state)
            (PState root_state)) = None")
      case True
      have event_eq:
        "wp_event
          (receive_composition_fri_challenge \<bind>
            (\<lambda>b. return ((s, root_state), (b, fri_root))))
          ?Q root_state =
         wp_event receive_composition_fri_challenge
          (\<lambda>out. case out of None \<Rightarrow> False | Some (b, _) \<Rightarrow> b \<in> ?B)
          root_state"
        unfolding wp_event_def
        apply (simp only: wp_bind)
        apply (rule arg_cong[
          where f = "\<lambda>R. wp receive_composition_fri_challenge R root_state"])
        apply (rule ext)
        apply (case_tac r)
         apply simp
        apply (rename_tac out)
        apply (case_tac out)
        by (simp add: wpsimps
          ro_composition_fri_online_bad_fresh_item_def True)
      have "wp_event
          (receive_composition_fri_challenge \<bind>
            (\<lambda>b. return ((s, root_state), (b, fri_root))))
          ?Q root_state =
        nnreal (card ?B) / nnreal size"
        unfolding event_eq
        by (rule wp_receive_composition_fri_challenge_fresh_set[OF True])
      also have "... \<le> nnreal 1 / nnreal size"
        by (rule nnreal_nat_divide_right_mono)
          (rule card_fri_online_bad_challenges_le_one)
      also have "... = 1 / nnreal size"
        by simp
      finally show ?thesis .
    next
      case False
      have cont_zero:
        "(\<lambda>r. case r of
            None \<Rightarrow> ?I None
          | Some (b, st) \<Rightarrow>
              wp (return ((s, root_state), (b, fri_root))) ?I st)
         = (\<lambda>_. 0)"
        apply (rule ext)
        apply (case_tac r)
         apply simp
        apply (rename_tac out)
        apply (case_tac out)
        by (simp add: wpsimps
          ro_composition_fri_online_bad_fresh_item_def False)
      have event_false:
        "wp_event
          (receive_composition_fri_challenge \<bind>
            (\<lambda>b. return ((s, root_state), (b, fri_root))))
          ?Q root_state = 0"
        unfolding wp_event_def
        apply (simp only: wp_bind cont_zero)
        unfolding wp_def dist_expect_def
        by simp
      show ?thesis
        unfolding event_false by simp
    qed
    show
      "wp_event
        (get \<bind>
          (\<lambda>root_state. receive_composition_fri_challenge \<bind>
            (\<lambda>b. return ((s, root_state), (b, fri_root)))))
        ?Q root_state
      \<le> 1 / nnreal size"
      unfolding get_event_eq
      by (rule challenge_bound)
  qed
qed

fun indexed_list_hit
  :: "(nat \<Rightarrow> 'x \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'x list \<Rightarrow> bool"
where
  "indexed_list_hit P i [] = False"
| "indexed_list_hit P i (x # xs) =
    (P i x \<or> indexed_list_hit P (Suc i) xs)"

lemma indexed_list_hit_Cons:
  "indexed_list_hit P i (x # xs) \<longleftrightarrow>
    P i x \<or> indexed_list_hit P (Suc i) xs"
  by simp

lemma wp_ntimes_indexed_list_hit_bound:
  fixes step :: "('x, 's) state_monad"
    and P :: "nat \<Rightarrow> 'x \<Rightarrow> bool"
    and D :: nnreal
  assumes one_step:
    "\<And>s i. wp_event step
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (x, _) \<Rightarrow> P i x) s \<le> 1 / D"
  shows
    "wp_event (ntimes step n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (xs, _) \<Rightarrow> indexed_list_hit P i xs) s
      \<le> nnreal n / D"
proof (induction n arbitrary: s i)
  case 0
  then show ?case
    by (simp add: wp_event_def wpsimps)
next
  case (Suc n)
  let ?tail =
    "ntimes step n :: ('x list, 's) state_monad"
  let ?Q =
    "\<lambda>out :: (('x list \<times> 's) option).
      case out of
        None \<Rightarrow> False
      | Some (xs, _) \<Rightarrow> indexed_list_hit P i xs"
  let ?Head =
    "\<lambda>out :: (('x \<times> 's) option).
      case out of
        None \<Rightarrow> False
      | Some (x, _) \<Rightarrow> P i x"
  let ?QHead =
    "\<lambda>out :: (('x list \<times> 's) option).
      case out of
        None \<Rightarrow> False
      | Some (xs, _) \<Rightarrow>
          (case xs of [] \<Rightarrow> False | x # _ \<Rightarrow> P i x)"
  let ?QTail =
    "\<lambda>out :: (('x list \<times> 's) option).
      case out of
        None \<Rightarrow> False
      | Some (xs, _) \<Rightarrow>
          (case xs of
             [] \<Rightarrow> False
           | _ # xs' \<Rightarrow> indexed_list_hit P (Suc i) xs')"
  have head_once: "wp_event step ?Head s \<le> 1 / D"
    by (rule one_step)
  have head_bound:
      "wp_event (ntimes step (Suc n)) ?QHead s \<le> 1 / D"
  proof -
    have
      "wp_event
        (step \<bind> (\<lambda>x. ?tail \<bind> (\<lambda>xs. return (x # xs))))
        ?QHead s \<le> 1 / D"
    proof (rule wp_event_bind_bound_by_head_event[OF head_once])
      show "?QHead None \<Longrightarrow> ?Head None"
        by simp
    next
      fix x t out
      assume head_out:
          "Some (x, t) \<in> set_dist (execute step s)"
        and cont_out:
          "out \<in> set_dist
            (execute (?tail \<bind> (\<lambda>xs. return (x # xs))) t)"
        and hit: "?QHead out"
      show "?Head (Some (x, t))"
        using cont_out hit
        by (auto elim!: set_dist_bindE
          split: option.splits prod.splits list.splits)
    qed
    then show ?thesis
      by simp
  qed
  have tail_bound:
      "wp_event (ntimes step (Suc n)) ?QTail s \<le> nnreal n / D"
  proof -
    have
      "wp_event
        (step \<bind> (\<lambda>x. ?tail \<bind> (\<lambda>xs. return (x # xs))))
        ?QTail s \<le> nnreal n / D"
    proof (rule wp_event_bind_bound_by_cont)
      show "\<not> ?QTail None"
        by simp
    next
      fix x t
      assume head_out:
        "Some (x, t) \<in> set_dist (execute step s)"
      let ?TailP =
        "\<lambda>out :: (('x list \<times> 's) option).
          case out of
            None \<Rightarrow> False
          | Some (xs, _) \<Rightarrow> indexed_list_hit P (Suc i) xs"
      have tail_ih:
          "wp_event ?tail ?TailP t \<le> nnreal n / D"
        by (rule Suc.IH)
      have cont_eq:
          "wp_event (?tail \<bind> (\<lambda>xs. return (x # xs))) ?QTail t =
           wp_event ?tail ?TailP t"
        unfolding wp_event_def
        apply (simp only: wp_bind)
        apply (rule arg_cong[where f = "\<lambda>R. wp ?tail R t"])
        apply (rule ext)
        apply (case_tac r)
         apply simp
        apply (rename_tac out)
        apply (case_tac out)
        by (simp add: wpsimps)
      show
        "wp_event (?tail \<bind> (\<lambda>xs. return (x # xs)))
          ?QTail t \<le> nnreal n / D"
        unfolding cont_eq
        by (rule tail_ih)
    qed
    then show ?thesis
      by simp
  qed
  have split:
      "wp_event (ntimes step (Suc n)) ?Q s \<le>
        wp_event (ntimes step (Suc n))
          (\<lambda>out. ?QHead out \<or> ?QTail out) s"
    by (rule wp_event_mono)
      (auto split: option.splits prod.splits list.splits)
  also have "... \<le>
      wp_event (ntimes step (Suc n)) ?QHead s +
      wp_event (ntimes step (Suc n)) ?QTail s"
    by (rule wp_event_union_bound)
  also have "... \<le> 1 / D + nnreal n / D"
    by (rule add_mono[OF head_bound tail_bound])
  also have "... = nnreal (Suc n) / D"
    by (simp add: add_divide_nnreal add.commute)
  finally show ?case .
qed

lemma wp_ntimes_ro_receive_trace_fri_commits_with_prefix_online_bad_fresh_bound:
  "wp_event (ntimes ro_receive_trace_fri_commits_with_prefix n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (xs, _) \<Rightarrow>
            indexed_list_hit (ro_trace_fri_online_bad_fresh_item d) i xs) s
    \<le> nnreal n / nnreal size"
  by (rule wp_ntimes_indexed_list_hit_bound)
    (rule wp_ro_receive_trace_fri_commits_with_prefix_online_bad_fresh_bound)

lemma wp_ntimes_ro_receive_composition_fri_commits_with_prefix_online_bad_fresh_bound:
  "wp_event (ntimes ro_receive_composition_fri_commits_with_prefix n)
      (\<lambda>out. case out of
          None \<Rightarrow> False
        | Some (xs, _) \<Rightarrow>
            indexed_list_hit
              (ro_composition_fri_online_bad_fresh_item d) i xs) s
    \<le> nnreal n / nnreal size"
  by (rule wp_ntimes_indexed_list_hit_bound)
    (rule wp_ro_receive_composition_fri_commits_with_prefix_online_bad_fresh_bound)

lemma ro_receive_trace_fri_commits_with_prefix_projection:
  "ro_receive_trace_fri_commits_with_prefix \<bind>
      (\<lambda>item. return (snd item)) =
    ro_receive_trace_fri_commits"
  unfolding
    ro_receive_trace_fri_commits_with_prefix_def
    ro_receive_trace_fri_commits_def
    ro_receive_fri_commits_with_def
  by (simp add: sm_bind_assoc sm_bind_get_ignore)

lemma wp_event_ro_receive_trace_fri_commits_with_prefix_projection:
  "wp_event
      (ro_receive_trace_fri_commits_with_prefix \<bind>
        (\<lambda>item. k (snd item))) Q s =
    wp_event (ro_receive_trace_fri_commits \<bind> k) Q s"
proof -
  have program_eq:
    "ro_receive_trace_fri_commits_with_prefix \<bind>
        (\<lambda>item. k (snd item)) =
      ro_receive_trace_fri_commits \<bind> k"
  proof -
    have
      "ro_receive_trace_fri_commits_with_prefix \<bind>
          (\<lambda>item. k (snd item)) =
        (ro_receive_trace_fri_commits_with_prefix \<bind>
          (\<lambda>item. return (snd item))) \<bind> k"
      by (simp add: sm_bind_assoc)
    also have "... = ro_receive_trace_fri_commits \<bind> k"
      by (simp only:
        ro_receive_trace_fri_commits_with_prefix_projection)
    finally show ?thesis .
  qed
  show ?thesis
    by (simp only: program_eq)
qed

lemma ro_receive_composition_fri_commits_with_prefix_projection:
  "ro_receive_composition_fri_commits_with_prefix \<bind>
      (\<lambda>item. return (snd item)) =
    ro_receive_composition_fri_commits"
  unfolding
    ro_receive_composition_fri_commits_with_prefix_def
    ro_receive_composition_fri_commits_def
    ro_receive_fri_commits_with_def
  by (simp add: sm_bind_assoc sm_bind_get_ignore)

lemma wp_event_ro_receive_composition_fri_commits_with_prefix_projection:
  "wp_event
      (ro_receive_composition_fri_commits_with_prefix \<bind>
        (\<lambda>item. k (snd item))) Q s =
    wp_event (ro_receive_composition_fri_commits \<bind> k) Q s"
proof -
  have program_eq:
    "ro_receive_composition_fri_commits_with_prefix \<bind>
        (\<lambda>item. k (snd item)) =
      ro_receive_composition_fri_commits \<bind> k"
  proof -
    have
      "ro_receive_composition_fri_commits_with_prefix \<bind>
          (\<lambda>item. k (snd item)) =
        (ro_receive_composition_fri_commits_with_prefix \<bind>
          (\<lambda>item. return (snd item))) \<bind> k"
      by (simp add: sm_bind_assoc)
    also have "... = ro_receive_composition_fri_commits \<bind> k"
      by (simp only:
        ro_receive_composition_fri_commits_with_prefix_projection)
    finally show ?thesis .
  qed
  show ?thesis
    by (simp only: program_eq)
qed

lemma ntimes_projection:
  fixes annotated :: "('x, 's) state_monad"
    and actual :: "('y, 's) state_monad"
  assumes one_step:
    "annotated \<bind> (\<lambda>x. return (project x)) = actual"
  shows
    "ntimes annotated n \<bind> (\<lambda>xs. return (map project xs)) =
      ntimes actual n"
  using one_step
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have ih:
    "ntimes annotated n \<bind> (\<lambda>xs. return (map project xs)) =
      ntimes actual n"
    by (rule Suc.IH[OF Suc.prems])
  have cont_eq:
    "\<And>x. ntimes annotated n \<bind>
        (\<lambda>xs. return (x # map project xs)) =
      ntimes actual n \<bind> (\<lambda>ys. return (x # ys))"
  proof -
    fix x
    have
      "ntimes annotated n \<bind>
          (\<lambda>xs. return (x # map project xs)) =
        (ntimes annotated n \<bind>
          (\<lambda>xs. return (map project xs))) \<bind>
          (\<lambda>ys. return (x # ys))"
      by (simp add: sm_bind_assoc)
    also have "... = ntimes actual n \<bind> (\<lambda>ys. return (x # ys))"
      by (simp only: ih)
    finally show
      "ntimes annotated n \<bind>
          (\<lambda>xs. return (x # map project xs)) =
        ntimes actual n \<bind> (\<lambda>ys. return (x # ys))" .
  qed
  have head_eq:
    "annotated \<bind>
        (\<lambda>x. ntimes annotated n \<bind>
          (\<lambda>xs. return (project x # map project xs))) =
      actual \<bind>
        (\<lambda>x. ntimes annotated n \<bind>
          (\<lambda>xs. return (x # map project xs)))"
  proof -
    have
      "annotated \<bind>
          (\<lambda>x. ntimes annotated n \<bind>
            (\<lambda>xs. return (project x # map project xs))) =
        (annotated \<bind> (\<lambda>x. return (project x))) \<bind>
          (\<lambda>x. ntimes annotated n \<bind>
            (\<lambda>xs. return (x # map project xs)))"
      by (simp add: sm_bind_assoc)
    also have "... = actual \<bind>
        (\<lambda>x. ntimes annotated n \<bind>
          (\<lambda>xs. return (x # map project xs)))"
      by (simp only: Suc.prems)
    finally show ?thesis .
  qed
  have
    "ntimes annotated (Suc n) \<bind>
        (\<lambda>xs. return (map project xs)) =
      annotated \<bind>
        (\<lambda>x. ntimes annotated n \<bind>
          (\<lambda>xs. return (project x # map project xs)))"
    by (simp add: sm_bind_assoc)
  also have "... = actual \<bind>
      (\<lambda>x. ntimes annotated n \<bind>
        (\<lambda>xs. return (x # map project xs)))"
    by (rule head_eq)
  also have "... = actual \<bind>
      (\<lambda>x. ntimes actual n \<bind> (\<lambda>xs. return (x # xs)))"
    by (simp only: cont_eq)
  also have "... = ntimes actual (Suc n)"
    by simp
  finally show ?case .
qed

lemma ntimes_projection_cont:
  fixes annotated :: "('x, 's) state_monad"
    and actual :: "('y, 's) state_monad"
  assumes one_step:
    "annotated \<bind> (\<lambda>x. return (project x)) = actual"
  shows
    "ntimes annotated n \<bind>
        (\<lambda>xs. k (map project xs)) =
      ntimes actual n \<bind> k"
proof -
  have list_projection:
    "ntimes annotated n \<bind>
        (\<lambda>xs. return (map project xs)) =
      ntimes actual n"
    by (rule ntimes_projection[OF one_step])
  have
    "ntimes annotated n \<bind>
        (\<lambda>xs. k (map project xs)) =
      (ntimes annotated n \<bind>
        (\<lambda>xs. return (map project xs))) \<bind> k"
    by (simp add: sm_bind_assoc)
  also have "... = ntimes actual n \<bind> k"
    by (simp only: list_projection)
  finally show ?thesis .
qed

lemma wp_event_ntimes_projection:
  fixes annotated :: "('x, 's) state_monad"
    and actual :: "('y, 's) state_monad"
  assumes one_step:
    "annotated \<bind> (\<lambda>x. return (project x)) = actual"
  shows
    "wp_event
        (ntimes annotated n \<bind>
          (\<lambda>xs. k (map project xs))) Q s =
      wp_event (ntimes actual n \<bind> k) Q s"
proof -
  have list_projection:
    "ntimes annotated n \<bind>
        (\<lambda>xs. return (map project xs)) =
      ntimes actual n"
    by (rule ntimes_projection[OF one_step])
  have program_eq:
    "ntimes annotated n \<bind>
        (\<lambda>xs. k (map project xs)) =
      ntimes actual n \<bind> k"
  proof -
    have
      "ntimes annotated n \<bind>
          (\<lambda>xs. k (map project xs)) =
        (ntimes annotated n \<bind>
          (\<lambda>xs. return (map project xs))) \<bind> k"
      by (simp add: sm_bind_assoc)
    also have "... = ntimes actual n \<bind> k"
      by (simp only: list_projection)
    finally show ?thesis .
  qed
  show ?thesis
    by (simp only: program_eq)
qed

lemma ntimes_ro_receive_trace_fri_commits_with_prefix_projection_cont:
  "ntimes ro_receive_trace_fri_commits_with_prefix n \<bind>
      (\<lambda>xs. k (map snd xs)) =
    ntimes ro_receive_trace_fri_commits n \<bind> k"
  by (rule ntimes_projection_cont)
    (rule ro_receive_trace_fri_commits_with_prefix_projection)

lemma ntimes_ro_receive_composition_fri_commits_with_prefix_projection_cont:
  "ntimes ro_receive_composition_fri_commits_with_prefix n \<bind>
      (\<lambda>xs. k (map snd xs)) =
    ntimes ro_receive_composition_fri_commits n \<bind> k"
  by (rule ntimes_projection_cont)
    (rule ro_receive_composition_fri_commits_with_prefix_projection)

lemma ntimes_ro_receive_trace_fri_commits_with_prefix_projection:
  "ntimes ro_receive_trace_fri_commits_with_prefix n \<bind>
      (\<lambda>xs. return (map snd xs)) =
    ntimes ro_receive_trace_fri_commits n"
  by (rule ntimes_projection)
    (rule ro_receive_trace_fri_commits_with_prefix_projection)

lemma ntimes_ro_receive_composition_fri_commits_with_prefix_projection:
  "ntimes ro_receive_composition_fri_commits_with_prefix n \<bind>
      (\<lambda>xs. return (map snd xs)) =
    ntimes ro_receive_composition_fri_commits n"
  by (rule ntimes_projection)
    (rule ro_receive_composition_fri_commits_with_prefix_projection)

lemma wp_event_ntimes_ro_receive_trace_fri_commits_with_prefix_projection:
  "wp_event
      (ntimes ro_receive_trace_fri_commits_with_prefix n \<bind>
        (\<lambda>xs. k (map snd xs))) Q s =
    wp_event (ntimes ro_receive_trace_fri_commits n \<bind> k) Q s"
  by (rule wp_event_ntimes_projection)
    (rule ro_receive_trace_fri_commits_with_prefix_projection)

lemma wp_event_ntimes_ro_receive_composition_fri_commits_with_prefix_projection:
  "wp_event
      (ntimes ro_receive_composition_fri_commits_with_prefix n \<bind>
        (\<lambda>xs. k (map snd xs))) Q s =
    wp_event (ntimes ro_receive_composition_fri_commits n \<bind> k) Q s"
  by (rule wp_event_ntimes_projection)
    (rule ro_receive_composition_fri_commits_with_prefix_projection)

end

end