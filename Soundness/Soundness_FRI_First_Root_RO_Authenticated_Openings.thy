(*  Title:      Stark/Soundness_FRI_First_Root_RO_Authenticated_Openings.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_Authenticated_Openings
  imports Soundness_FRI_First_Root_RO_Security_Query_Bound
begin

text \<open>
  Exact partial-opening evidence for the domain-separated absorbing verifier.
  Successful RO query rounds authenticate the trace root and the first trace-FRI
  root at the same actual sampled index.  The final lift uses only prefix-fixed
  conceptual tables and charges later disagreement to a first-fresh Merkle
  target.
\<close>

context soundness
begin

lemma ro_query_decommitment_step_authenticated_opening:
  fixes s t :: "'f protocol_channel"
  assumes idx_bound: "idx < scale * clength"
    and outcome:
      "Some (qh, t) \<in> set_dist (execute (ro_query_decommitment_step rt idx) s)"
  obtains path opn where
    "opn =
      \<lparr>opening_root = rt,
       opening_length = scale * clength,
       opening_index = idx,
       opening_value = qh,
       opening_path = path\<rparr>"
    "authenticated_opening_in t opn"
proof -
  let ?len = "scale * clength"
  from outcome obtain s1 path s2 ap s3 s4 where
    read_qh:
      "Some (qh, s1) \<in> set_dist (execute protocol_absorb_read s)"
    and read_path:
      "Some (path, s2) \<in>
        set_dist (execute (ntimes protocol_absorb_read (floor_log ?len)) s1)"
    and check:
      "Some (ap, s3) \<in>
        set_dist (execute (check_authentication_path ?len idx qh path) s2)"
    and assert_ap:
      "Some ((), s4) \<in> set_dist (execute (assert (ap = rt)) s3)"
    and ret:
      "Some (qh, t) \<in> set_dist (execute (return qh) s4)"
    unfolding ro_query_decommitment_step_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  have path_len: "length path = floor_log ?len"
    using ntimes_protocol_absorb_read_outcome_with_lookup_chain[OF read_path]
    by blast
  have ap_eq: "ap = rt"
    using assert_ap unfolding assert_def
    by (cases "ap = rt") (auto simp: throw_no_outcome)
  have s4_eq: "s4 = s3"
    using assert_ap ap_eq unfolding assert_def by simp
  have t_eq: "t = s3"
    using ret s4_eq by simp
  have bound: "merkle_path_bound rt ?len idx qh path t"
  proof -
    have "merkle_path_bound ap ?len idx qh path s3"
      by (rule check_authentication_path_outcome_bound[OF check])
    then show ?thesis
      using ap_eq t_eq by simp
  qed
  let ?opn =
    "\<lparr>opening_root = rt,
      opening_length = ?len,
      opening_index = idx,
      opening_value = qh,
      opening_path = path\<rparr>"
  have auth: "authenticated_opening_in t ?opn"
    unfolding authenticated_opening_in_def
    using idx_bound path_len bound by simp
  show ?thesis
    by (rule that[of ?opn path]) (use auth in simp_all)
qed

lemma ro_mmap_query_decommitment_steps_authenticated_openings:
  fixes s t :: "'f protocol_channel"
  assumes idxs_bound: "\<And>idx. idx \<in> set idxs \<Longrightarrow> idx < scale * clength"
    and outcome:
      "Some (leaves, t) \<in>
        set_dist
          (execute (mmap (map (ro_query_decommitment_step rt) idxs)) s)"
  shows
    "\<exists>openings.
      length openings = length idxs \<and>
      map opening_value openings = leaves \<and>
      map opening_index openings = idxs \<and>
      partial_authenticated_table rt (scale * clength) openings t"
  using outcome idxs_bound
proof (induction idxs arbitrary: s leaves t)
  case Nil
  then have "leaves = []" and "t = s"
    by simp_all
  moreover have
    "partial_authenticated_table rt (scale * clength) [] t"
    unfolding partial_authenticated_table_def by simp
  ultimately show ?case
    by (intro exI[of _ "[]"]) simp
next
  case (Cons idx idxs)
  from Cons.prems obtain leaf leaves' s1 where
    head:
      "Some (leaf, s1) \<in>
        set_dist (execute (ro_query_decommitment_step rt idx) s)"
    and tail:
      "Some (leaves', t) \<in>
        set_dist
          (execute (mmap (map (ro_query_decommitment_step rt) idxs)) s1)"
    and leaves_eq: "leaves = leaf # leaves'"
    by (auto elim!: set_dist_bindE)
  have idx_bound: "idx < scale * clength"
    by (rule Cons.prems(2)) simp
  from ro_query_decommitment_step_authenticated_opening[OF idx_bound head]
  obtain path opn where
    opn_eq:
      "opn =
        \<lparr>opening_root = rt,
         opening_length = scale * clength,
         opening_index = idx,
         opening_value = leaf,
         opening_path = path\<rparr>"
    and opn_auth_s1: "authenticated_opening_in s1 opn"
    by blast
  have tail_bound:
    "\<And>j. j \<in> set idxs \<Longrightarrow> j < scale * clength"
    by (rule Cons.prems(2)) simp
  from Cons.IH[OF tail tail_bound]
  obtain openings where
    len_openings: "length openings = length idxs"
    and values_openings: "map opening_value openings = leaves'"
    and idx_openings: "map opening_index openings = idxs"
    and table_tail:
      "partial_authenticated_table rt (scale * clength) openings t"
    by blast
  have s1_t: "s1 \<le> t"
    using mmap_ro_query_decommitment_steps_outcome_with_lookup_chain[OF tail]
    by blast
  have opn_auth_t: "authenticated_opening_in t opn"
    by (rule authenticated_opening_in_mono[OF opn_auth_s1 s1_t])
  let ?openings = "opn # openings"
  have table_all:
    "partial_authenticated_table rt (scale * clength) ?openings t"
    using opn_auth_t table_tail opn_eq
    unfolding partial_authenticated_table_def by simp
  show ?case
    using len_openings values_openings idx_openings leaves_eq opn_eq table_all
    by (intro exI[of _ ?openings]) simp
qed

lemma ro_check_decommit_on_query_authenticated_openings:
  fixes s t :: "'f protocol_channel"
  assumes idx_in: "idx \<in> query_sample_space"
    and outcome:
      "Some (leaves, t) \<in>
        set_dist (execute (mmap (ro_check_decommit_on_query rt idx)) s)"
  obtains openings where
    "length openings = length (powers_scaled idx)"
    "map opening_value openings = leaves"
    "map opening_index openings = powers_scaled idx"
    "partial_authenticated_table rt (scale * clength) openings t"
proof -
  have map_eq:
    "ro_check_decommit_on_query rt idx =
      map (ro_query_decommitment_step rt) (powers_scaled idx)"
    unfolding ro_check_decommit_on_query_def by simp
  have idxs_bound:
    "\<And>i. i \<in> set (powers_scaled idx) \<Longrightarrow> i < scale * clength"
    using query_sample_space_powers_scaled_bound[OF idx_in]
    by (simp add: mult.commute)
  from ro_mmap_query_decommitment_steps_authenticated_openings
      [OF idxs_bound outcome[unfolded map_eq]]
  obtain openings where
    "length openings = length (powers_scaled idx)"
    "map opening_value openings = leaves"
    "map opening_index openings = powers_scaled idx"
    "partial_authenticated_table rt (scale * clength) openings t"
    by blast
  then show ?thesis
    by (rule that)
qed

lemma ro_fri_layer_opening_step_partial_authenticated_table_first_value:
  fixes s t :: "'f protocol_channel"
  assumes len_pos: "0 < len"
    and idx_bound: "idx < len"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (ro_fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
  obtains openings where
    "partial_authenticated_table rt len openings t"
    "map opening_index openings = [idx, (idx + len div 2) mod len]"
    "length openings = 2"
    "opening_value (openings ! 0) = x"
proof -
  from outcome obtain xp s1 xp_path s2 xn s3 xn_path s4 where
    read_xp:
      "Some (xp, s1) \<in> set_dist (execute protocol_absorb_read s)"
    and read_xp_path:
      "Some (xp_path, s2) \<in>
        set_dist (execute (ntimes protocol_absorb_read (floor_log len)) s1)"
    and read_xn:
      "Some (xn, s3) \<in> set_dist (execute protocol_absorb_read s2)"
    and read_xn_path:
      "Some (xn_path, s4) \<in>
        set_dist (execute (ntimes protocol_absorb_read (floor_log len)) s3)"
    and finish:
      "Some (out, t) \<in>
        set_dist
          (execute
            (fri_layer_opening_finish b rt idx x len pw
              xp xp_path xn xn_path) s4)"
    unfolding ro_fri_layer_opening_step_def
    by (auto elim!: set_dist_bindE)
  have xp_path_length: "length xp_path = floor_log len"
    using ntimes_protocol_absorb_read_outcome_with_lookup_chain[OF read_xp_path]
    by blast
  have xn_path_length: "length xn_path = floor_log len"
    using ntimes_protocol_absorb_read_outcome_with_lookup_chain[OF read_xn_path]
    by blast
  have sibling_bound: "(idx + len div 2) mod len < len"
    using len_pos by simp
  have xp_x: "xp = x"
    using finish
    unfolding fri_layer_opening_finish_def assert_def
    by (auto simp: throw_no_outcome elim!: set_dist_bindE split: if_splits)
  from fri_layer_opening_finish_authenticated_openings
      [OF idx_bound sibling_bound xp_path_length xn_path_length finish]
  obtain xp_opening xn_opening where
    xp_eq:
      "xp_opening =
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path\<rparr>"
    and xn_eq:
      "xn_opening =
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = (idx + len div 2) mod len,
         opening_value = xn,
         opening_path = xn_path\<rparr>"
    and xp_auth: "authenticated_opening_in t xp_opening"
    and xn_auth: "authenticated_opening_in t xn_opening"
    by blast
  let ?openings = "[xp_opening, xn_opening]"
  have table: "partial_authenticated_table rt len ?openings t"
    unfolding partial_authenticated_table_def
    using xp_eq xn_eq xp_auth xn_auth by simp
  have indices:
    "map opening_index ?openings = [idx, (idx + len div 2) mod len]"
    using xp_eq xn_eq by simp
  have first_value: "opening_value (?openings ! 0) = x"
    using xp_eq xp_x by simp
  show ?thesis
    by (rule that[OF table indices _ first_value]) simp
qed

lemma mfold_ro_receive_query_commits_first_partial_authenticated_table:
  fixes s t :: "'f protocol_channel"
  assumes bfs_eq: "bfs = (b, rt) # bfs_tail"
    and len_pos: "0 < len"
    and idx_bound: "idx < len"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw) (ro_receive_query_commits bfs)) s)"
  obtains openings where
    "partial_authenticated_table rt len openings t"
    "map opening_index openings = [idx, (idx + len div 2) mod len]"
    "length openings = 2"
    "opening_value (openings ! 0) = x"
proof -
  from outcome obtain out1 s1 where
    head:
      "Some (out1, s1) \<in>
        set_dist
          (execute
            (ro_fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold out1
              (map ro_fri_layer_opening_step bfs_tail)) s1)"
    unfolding ro_receive_query_commits_def bfs_eq
    by (auto elim!: set_dist_bindE)
  from ro_fri_layer_opening_step_partial_authenticated_table_first_value
      [OF len_pos idx_bound head]
  obtain openings where
    table_s1: "partial_authenticated_table rt len openings s1"
    and indices:
      "map opening_index openings = [idx, (idx + len div 2) mod len]"
    and openings_len: "length openings = 2"
    and first_value: "opening_value (openings ! 0) = x"
    by blast
  have s1_t: "s1 \<le> t"
    using mfold_ro_fri_layer_opening_steps_outcome_extends_counter[OF tail]
    by blast
  have table_t: "partial_authenticated_table rt len openings t"
    by (rule partial_authenticated_table_mono[OF table_s1 s1_t])
  show ?thesis
    by (rule that[OF table_t indices openings_len first_value])
qed

lemma ro_verifier_query_round_program_authenticated_trace_first_fri_openings:
  fixes s t :: "'f protocol_channel"
  assumes f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (ro_verifier_query_round_program
              fr f_fl f_final as fl final) s)"
  obtains raw idx fv trace_openings first_openings where
    "idx = index (to_nat raw)"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    "length trace_openings = length (powers_scaled idx)"
    "map opening_value trace_openings = fv"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table rt (scale * clength) first_openings t"
    "map opening_index first_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    "length first_openings = 2"
    "opening_value (trace_openings ! 0) =
      opening_value (first_openings ! 0)"
proof -
  from outcome obtain raw s1 fv s2 f_i f_x f_len f_pow s3 s4
      i x len pw s5 where
    challenge:
      "Some (raw, s1) \<in> set_dist (execute receive_query_index_challenge s)"
    and decommit:
      "Some (fv, s2) \<in>
        set_dist
          (execute
            (mmap (ro_check_decommit_on_query fr (index (to_nat raw)))) s1)"
    and trace_fri:
      "Some ((f_i, f_x, f_len, f_pow), s3) \<in>
        set_dist
          (execute
            (mfold (index (to_nat raw), hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl)) s2)"
    and trace_assert:
      "Some ((), s4) \<in> set_dist (execute (assert (f_x = f_final)) s3)"
    and composition_fri:
      "Some ((i, x, len, pw), s5) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat raw),
                cp_eval as fv (h ^ index (to_nat raw) * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl)) s4)"
    and composition_assert:
      "Some ((), t) \<in> set_dist (execute (assert (x = final)) s5)"
    unfolding ro_verifier_query_round_program_def
    by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)
  let ?idx = "index (to_nat raw)"
  have idx_sample: "?idx \<in> query_sample_space"
    using index_less_query_sample_space
    unfolding query_sample_space_def by simp
  from ro_check_decommit_on_query_authenticated_openings
      [OF idx_sample decommit]
  obtain trace_openings where
    trace_len:
      "length trace_openings = length (powers_scaled ?idx)"
    and trace_values: "map opening_value trace_openings = fv"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled ?idx"
    and trace_table_s2:
      "partial_authenticated_table fr (scale * clength) trace_openings s2"
    by blast
  have domain_pos: "0 < clength * scale"
    using eval_domain_nontrivial by linarith
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  from mfold_ro_receive_query_commits_first_partial_authenticated_table
      [OF f_fl_eq domain_pos idx_bound trace_fri]
  obtain first_openings where
    first_table_s3:
      "partial_authenticated_table rt (clength * scale) first_openings s3"
    and first_indices0:
      "map opening_index first_openings =
        [?idx, (?idx + (clength * scale) div 2) mod (clength * scale)]"
    and first_len: "length first_openings = 2"
    and first_value:
      "opening_value (first_openings ! 0) = hd fv"
    by blast
  have s2_s3: "s2 \<le> s3"
    using ro_receive_query_commits_outcome_extends_counter[OF trace_fri]
    by blast
  have s4_eq: "s4 = s3"
    using trace_assert unfolding assert_def
    by (cases "f_x = f_final") (auto simp: throw_no_outcome)
  have s4_s5: "s4 \<le> s5"
    using ro_receive_query_commits_outcome_extends_counter[OF composition_fri]
    by blast
  have t_eq: "t = s5"
    using composition_assert unfolding assert_def
    by (cases "x = final") (auto simp: throw_no_outcome)
  have s2_t: "s2 \<le> t"
    using s2_s3 s4_s5 unfolding s4_eq t_eq
    by (rule hash_ext_trans)
  have s3_t: "s3 \<le> t"
    using s4_s5 unfolding s4_eq t_eq .
  have trace_table_t:
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    by (rule partial_authenticated_table_mono[OF trace_table_s2 s2_t])
  have first_table_t:
    "partial_authenticated_table rt (scale * clength) first_openings t"
    using partial_authenticated_table_mono[OF first_table_s3 s3_t]
    by (simp add: mult.commute)
  have first_indices:
    "map opening_index first_openings =
      [?idx, fri_sibling_index (scale * clength) ?idx]"
    using first_indices0
    unfolding fri_sibling_index_def
    by (simp add: mult.commute)
  have trace_nonempty: "trace_openings \<noteq> []"
  proof
    assume "trace_openings = []"
    then have "length trace_openings = 0"
      by simp
    then show False
      using trace_len powers_pos
      unfolding powers_scaled_def by simp
  qed
  have trace_first:
    "opening_value (trace_openings ! 0) = hd fv"
    using trace_values trace_nonempty
    by (cases trace_openings) auto
  have challenge_lookup_s1:
    "fmlookup (HashMap s1)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF challenge] by simp
  have s1_s2: "s1 \<le> s2"
    using ro_check_decommit_on_query_outcome_with_lookup_chain[OF decommit]
    by blast
  have s1_t: "s1 \<le> t"
    by (rule hash_ext_trans[OF s1_s2 s2_t])
  have lookup_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF challenge_lookup_s1 s1_t])
  show ?thesis
    by (rule that[of ?idx raw trace_openings fv first_openings])
      (use trace_len trace_values trace_indices trace_table_t first_table_t
        first_indices first_len trace_first first_value lookup_t in simp_all)
qed

lemma partial_authenticated_trace_first_fri_same_value_prefix_conceptual_agreement_or_target:
  fixes prefix_state final_state :: "'f protocol_channel"
  assumes ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and idx_sample: "idx \<in> query_sample_space"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and trace_table:
      "partial_authenticated_table fr (scale * clength)
        trace_openings final_state"
    and first_indices:
      "map opening_index first_openings =
        [idx, fri_sibling_index (scale * clength) idx]"
    and first_table:
      "partial_authenticated_table rt (scale * clength)
        first_openings final_state"
    and same_value:
      "opening_value (trace_openings ! 0) =
        opening_value (first_openings ! 0)"
  shows
    "idx \<in>
       trace_table_base_agreement_indices
         (conceptual_table prefix_state fr (scale * clength))
         (conceptual_table prefix_state rt (scale * clength)) \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {fr, rt} prefix_state)
       prefix_state final_state"
proof (cases
    "hash_map_new_output_hit
      (merkle_prefix_path_targets {fr, rt} prefix_state)
      prefix_state final_state")
  case True
  then show ?thesis by simp
next
  case False
  have fr_targets_subset:
    "merkle_prefix_path_targets {fr} prefix_state \<subseteq>
      merkle_prefix_path_targets {fr, rt} prefix_state"
    by (rule merkle_prefix_path_targets_mono) auto
  have rt_targets_subset:
    "merkle_prefix_path_targets {rt} prefix_state \<subseteq>
      merkle_prefix_path_targets {fr, rt} prefix_state"
    by (rule merkle_prefix_path_targets_mono) auto
  have no_fr:
    "\<not> hash_map_new_output_hit
      (merkle_prefix_path_targets {fr} prefix_state)
      prefix_state final_state"
  proof
    assume hit:
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {fr} prefix_state)
        prefix_state final_state"
    have "hash_map_new_output_hit
        (merkle_prefix_path_targets {fr, rt} prefix_state)
        prefix_state final_state"
      by (rule hash_map_new_output_hit_subset[OF fr_targets_subset hit])
    then show False
      using False by contradiction
  qed
  have no_rt:
    "\<not> hash_map_new_output_hit
      (merkle_prefix_path_targets {rt} prefix_state)
      prefix_state final_state"
  proof
    assume hit:
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {rt} prefix_state)
        prefix_state final_state"
    have "hash_map_new_output_hit
        (merkle_prefix_path_targets {fr, rt} prefix_state)
        prefix_state final_state"
      by (rule hash_map_new_output_hit_subset[OF rt_targets_subset hit])
    then show False
      using False by contradiction
  qed
  have trace_agrees:
    "table_agrees_with_authenticated_openings
      (conceptual_table prefix_state fr (scale * clength))
      (scale * clength) trace_openings"
    using
      partial_authenticated_table_agrees_with_prefix_conceptual_table_or_prefix_target_hit
        [OF ext clean trace_table]
      no_fr
    by blast
  have first_agrees:
    "table_agrees_with_authenticated_openings
      (conceptual_table prefix_state rt (scale * clength))
      (scale * clength) first_openings"
    using
      partial_authenticated_table_agrees_with_prefix_conceptual_table_or_prefix_target_hit
        [OF ext clean first_table]
      no_rt
    by blast
  have trace_nonempty: "trace_openings \<noteq> []"
  proof
    assume empty: "trace_openings = []"
    have "powers_scaled idx = []"
      using trace_indices empty by simp
    then show False
      using powers_pos unfolding powers_scaled_def by simp
  qed
  have first_nonempty: "first_openings \<noteq> []"
    using first_indices by auto
  have trace_head_index:
    "opening_index (trace_openings ! 0) = idx"
  proof -
    have
      "opening_index (trace_openings ! 0) =
        hd (map opening_index trace_openings)"
      using trace_nonempty by (cases trace_openings) simp_all
    also have "... = hd (powers_scaled idx)"
      using trace_indices by simp
    also have "... = idx"
      by (rule powers_scaled_hd)
    finally show ?thesis .
  qed
  have first_head_index:
    "opening_index (first_openings ! 0) = idx"
    using first_indices first_nonempty
    by (cases first_openings) auto
  have trace_head_in: "trace_openings ! 0 \<in> set trace_openings"
    using trace_nonempty by (cases trace_openings) simp_all
  have first_head_in: "first_openings ! 0 \<in> set first_openings"
    using first_nonempty by (cases first_openings) simp_all
  have trace_value:
    "conceptual_table prefix_state fr (scale * clength) ! idx =
      opening_value (trace_openings ! 0)"
    using trace_agrees trace_head_in trace_head_index
    unfolding table_agrees_with_authenticated_openings_def
    by blast
  have first_value:
    "conceptual_table prefix_state rt (scale * clength) ! idx =
      opening_value (first_openings ! 0)"
    using first_agrees first_head_in first_head_index
    unfolding table_agrees_with_authenticated_openings_def
    by blast
  have
    "idx \<in>
      trace_table_base_agreement_indices
        (conceptual_table prefix_state fr (scale * clength))
        (conceptual_table prefix_state rt (scale * clength))"
    unfolding trace_table_base_agreement_indices_def
    using idx_sample trace_value first_value same_value by simp
  then show ?thesis by simp
qed

lemma partial_authenticated_trace_first_fri_query_list_prefix_conceptual_agreement_or_target:
  fixes prefix_state final_state :: "'f protocol_channel"
  assumes query_len: "length query_idxs = rounds"
    and query_sample: "set query_idxs \<subseteq> query_sample_space"
    and ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and evidence:
      "\<And>i. i < length query_idxs \<Longrightarrow>
        map opening_index (trace_openings_at i) =
          powers_scaled (query_idxs ! i) \<and>
        partial_authenticated_table fr (scale * clength)
          (trace_openings_at i) final_state \<and>
        map opening_index (first_openings_at i) =
          [query_idxs ! i,
            fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
        partial_authenticated_table rt (scale * clength)
          (first_openings_at i) final_state \<and>
        opening_value (trace_openings_at i ! 0) =
          opening_value (first_openings_at i ! 0)"
  shows
    "query_idxs \<in>
       trace_table_base_agreement_query_lists
         (conceptual_table prefix_state fr (scale * clength))
         (conceptual_table prefix_state rt (scale * clength)) \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {fr, rt} prefix_state)
       prefix_state final_state"
proof (cases
    "hash_map_new_output_hit
      (merkle_prefix_path_targets {fr, rt} prefix_state)
      prefix_state final_state")
  case True
  then show ?thesis by simp
next
  case False
  have base_subset:
    "set query_idxs \<subseteq>
      trace_table_base_agreement_indices
        (conceptual_table prefix_state fr (scale * clength))
        (conceptual_table prefix_state rt (scale * clength))"
  proof (rule subsetI)
    fix idx
    assume idx_in: "idx \<in> set query_idxs"
    show
      "idx \<in>
        trace_table_base_agreement_indices
          (conceptual_table prefix_state fr (scale * clength))
          (conceptual_table prefix_state rt (scale * clength))"
    proof -
      from idx_in obtain i where i_bound: "i < length query_idxs"
      and idx_eq: "query_idxs ! i = idx"
      by (metis in_set_conv_nth)
      have ev:
        "map opening_index (trace_openings_at i) =
            powers_scaled (query_idxs ! i) \<and>
         partial_authenticated_table fr (scale * clength)
            (trace_openings_at i) final_state \<and>
         map opening_index (first_openings_at i) =
            [query_idxs ! i,
              fri_sibling_index (scale * clength) (query_idxs ! i)] \<and>
         partial_authenticated_table rt (scale * clength)
            (first_openings_at i) final_state \<and>
         opening_value (trace_openings_at i ! 0) =
            opening_value (first_openings_at i ! 0)"
        by (rule evidence[OF i_bound])
      have trace_indices:
        "map opening_index (trace_openings_at i) =
          powers_scaled (query_idxs ! i)"
        using ev by blast
      have trace_table:
        "partial_authenticated_table fr (scale * clength)
          (trace_openings_at i) final_state"
        using ev by blast
      have first_indices:
        "map opening_index (first_openings_at i) =
          [query_idxs ! i,
            fri_sibling_index (scale * clength) (query_idxs ! i)]"
        using ev by blast
      have first_table:
        "partial_authenticated_table rt (scale * clength)
          (first_openings_at i) final_state"
        using ev by blast
      have same_value:
        "opening_value (trace_openings_at i ! 0) =
          opening_value (first_openings_at i ! 0)"
        using ev by blast
    have idx_sample: "query_idxs ! i \<in> query_sample_space"
      using query_sample nth_mem[OF i_bound] by blast
    have
      "query_idxs ! i \<in>
        trace_table_base_agreement_indices
          (conceptual_table prefix_state fr (scale * clength))
          (conceptual_table prefix_state rt (scale * clength)) \<or>
       hash_map_new_output_hit
         (merkle_prefix_path_targets {fr, rt} prefix_state)
         prefix_state final_state"
      by (rule
          partial_authenticated_trace_first_fri_same_value_prefix_conceptual_agreement_or_target[
            OF ext clean idx_sample trace_indices trace_table first_indices
              first_table same_value])
    then show
      "idx \<in>
        trace_table_base_agreement_indices
          (conceptual_table prefix_state fr (scale * clength))
          (conceptual_table prefix_state rt (scale * clength))"
      using False idx_eq by blast
    qed
  qed
  have
    "query_idxs \<in>
      trace_table_base_agreement_query_lists
        (conceptual_table prefix_state fr (scale * clength))
        (conceptual_table prefix_state rt (scale * clength))"
    unfolding trace_table_base_agreement_query_lists_def
    using query_len query_sample base_subset by simp
  then show ?thesis by simp
qed

end
end
