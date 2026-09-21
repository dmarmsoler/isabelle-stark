theory Staged_Security_Experiment_RO_Query_Rectangle_Family_Future_Count
  imports
    Staged_Security_Experiment_RO_Query_List_Future_Count_Exact_Product
    Soundness_FRI_Conditioned_Query_Fiber
begin

context soundness
begin

text \<open>A verifier-tied family may be a union of structured rectangular query
events.  Bounding those rectangles directly avoids expanding each rectangle
into all of its singleton lists after adaptive future queries have already been
charged.\<close>

lemma wp_ro_checked_staged_query_program_index_rectangle_family_future_count_bound:
  assumes finite: "finite K"
    and cover:
      "Q \<subseteq> (\<Union>k\<in>K. fri_conditioned_query_lists (I k))"
    and len_qs: "length qs = n"
    and controlled:
      "\<forall>j < n. \<forall>raw.
        controlled_ro_program (qs ! j)
          (query_opening_stage A (i + j) raw)"
    and subsets: "\<forall>k\<in>K. I k \<subseteq> query_sample_space"
  shows
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A trace_roots
        composition_roots s i n)
      (ro_query_witnesses_index_list_set_hit Q) s \<le>
    (\<Sum>k\<in>K.
      (nnreal (query_raw_preimage_card_envelope (card (I k))) /
        nnreal size) ^
      (n - (query_future_prequery_count s + sum_list qs)))"
proof -
  let ?M =
    "ro_checked_staged_query_program_with_witnesses A trace_roots
      composition_roots s i n"
  have list_cover:
    "\<And>xs. xs \<in> Q \<Longrightarrow> \<exists>k\<in>K. set xs \<subseteq> I k"
  proof -
    fix xs
    assume xs_in: "xs \<in> Q"
    have xs_union:
      "xs \<in> (\<Union>k\<in>K. fri_conditioned_query_lists (I k))"
      by (rule set_mp[OF cover xs_in])
    then show "\<exists>k\<in>K. set xs \<subseteq> I k"
      unfolding fri_conditioned_query_lists_def by blast
  qed
  have eq_imp:
    "\<And>xs out indices.
      set xs \<subseteq> indices \<Longrightarrow>
      ro_query_witnesses_index_list_eq_hit xs out \<Longrightarrow>
      ro_query_witnesses_index_set_hit indices out"
    unfolding ro_query_witnesses_index_list_eq_hit_def
      ro_query_witnesses_index_set_hit_def
    by (auto split: option.splits prod.splits)
  have event_imp:
    "\<And>out. ro_query_witnesses_index_list_set_hit Q out \<Longrightarrow>
      \<exists>k\<in>K. ro_query_witnesses_index_set_hit (I k) out"
  proof -
    fix out
    assume hit: "ro_query_witnesses_index_list_set_hit Q out"
    then obtain xs where xs_in: "xs \<in> Q"
      and eq_hit: "ro_query_witnesses_index_list_eq_hit xs out"
      unfolding ro_query_witnesses_index_list_set_hit_def by blast
    from list_cover[OF xs_in] obtain k where k_in: "k \<in> K"
      and xs_subset: "set xs \<subseteq> I k"
      by blast
    have set_hit: "ro_query_witnesses_index_set_hit (I k) out"
      by (rule eq_imp[OF xs_subset eq_hit])
    show "\<exists>k\<in>K. ro_query_witnesses_index_set_hit (I k) out"
      using k_in set_hit by blast
  qed
  have mono:
    "wp_event ?M (ro_query_witnesses_index_list_set_hit Q) s \<le>
      wp_event ?M
        (\<lambda>out. \<exists>k\<in>K. ro_query_witnesses_index_set_hit (I k) out) s"
    by (rule wp_event_mono) (use event_imp in blast)
  have union:
    "wp_event ?M
        (\<lambda>out. \<exists>k\<in>K. ro_query_witnesses_index_set_hit (I k) out) s \<le>
      (\<Sum>k\<in>K.
        (nnreal (query_raw_preimage_card_envelope (card (I k))) /
          nnreal size) ^
        (n - (query_future_prequery_count s + sum_list qs)))"
  proof (rule wp_event_finite_union_bound[OF finite])
    fix k
    assume k_in: "k \<in> K"
    show
      "wp_event ?M (ro_query_witnesses_index_set_hit (I k)) s \<le>
        (nnreal (query_raw_preimage_card_envelope (card (I k))) /
          nnreal size) ^
        (n - (query_future_prequery_count s + sum_list qs))"
      by (rule wp_ro_checked_staged_query_program_index_set_future_count_bound[
            OF len_qs controlled])
        (use subsets k_in in blast)
  qed
  show ?thesis
    by (rule order_trans[OF mono union])
qed

end
end
