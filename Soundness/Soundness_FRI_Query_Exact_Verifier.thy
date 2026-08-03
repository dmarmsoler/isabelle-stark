(*  Title:      Stark/Soundness_FRI_Query_Exact_Verifier.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Query_Exact_Verifier
  imports Soundness_FRI_Query_Aware_Interface
begin

text \<open>
  Exact verifier-level consumption of sampled query-index lists.

  The query-aware interface defines the strict query-list events and proves
  exact bounds for the raw verifier query-round sequence.  This narrow layer
  lifts those bounds through the verifier decomposition.
\<close>

context soundness
begin

lemma query_rounds_index_list_hit_counter_eq:
  assumes counter: "PQueryCounter t = PQueryCounter s"
    and hit: "query_rounds_index_list_hit s query_idxs n out"
  shows "query_rounds_index_list_hit t query_idxs n out"
  using assms unfolding query_rounds_index_list_hit_def by auto

lemma wp_verifier_after_composition_fri_query_index_list_set_bound:
  assumes future: "query_future_fresh t"
    and counter: "PQueryCounter t = PQueryCounter s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (verifier_after_composition_fri header)
      (\<lambda>out. \<exists>query_idxs \<in> Q.
        query_rounds_index_list_hit s query_idxs rounds out) t \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
proof -
  obtain fr f_fl f_final as dg fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg, fl)"
    by (cases header) auto
  have after_eq:
    "verifier_after_composition_fri header =
      (read \<bind>
        (\<lambda>final.
          ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds))"
    unfolding header_eq verifier_after_composition_fri_def by simp
  show ?thesis
    unfolding after_eq
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> (\<exists>query_idxs\<in>Q.
        query_rounds_index_list_hit s query_idxs rounds None)"
      by simp
  next
    fix final query_state
    assume read_final:
      "Some (final, query_state) \<in> set_dist (execute read t)"
    have future_query: "query_future_fresh query_state"
      by (rule read_preserves_query_future_fresh[OF future read_final])
    from read_outcome[OF read_final] obtain rest where
      counter_query_t: "PQueryCounter query_state = PQueryCounter t"
      by blast
    have counter_query: "PQueryCounter query_state = PQueryCounter s"
      using counter_query_t counter by simp
    have event_mono:
      "wp_event
        (ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds)
        (\<lambda>out. \<exists>query_idxs\<in>Q.
          query_rounds_index_list_hit s query_idxs rounds out)
        query_state \<le>
       wp_event
        (ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds)
        (\<lambda>out. \<exists>query_idxs\<in>Q.
          query_rounds_index_list_hit query_state query_idxs rounds out)
        query_state"
    proof (rule wp_event_mono)
      fix out
      assume "\<exists>query_idxs\<in>Q.
        query_rounds_index_list_hit s query_idxs rounds out"
      then obtain query_idxs where
        query_in: "query_idxs \<in> Q"
        and hit: "query_rounds_index_list_hit s query_idxs rounds out"
        by blast
      have "query_rounds_index_list_hit query_state query_idxs rounds out"
        by (rule query_rounds_index_list_hit_counter_eq[OF counter_query hit])
      then show "\<exists>query_idxs\<in>Q.
        query_rounds_index_list_hit query_state query_idxs rounds out"
        using query_in by blast
    qed
    also have "... \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
      by (rule wp_ntimes_verifier_query_round_program_fri_index_list_set_bound
          [OF future_query raw_bound subset])
    finally show
      "wp_event
        (ntimes
          (verifier_query_round_program fr f_fl f_final as fl final)
          rounds)
        (\<lambda>out. \<exists>query_idxs\<in>Q.
          query_rounds_index_list_hit s query_idxs rounds out)
        query_state \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds" .
  qed
qed

lemma wp_verify_monad_query_index_list_set_bound:
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event verify_monad
      (\<lambda>out. \<exists>query_idxs \<in> Q.
        query_rounds_index_list_hit s query_idxs rounds out) s \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
  unfolding verify_monad_composition_fri_decomposition
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> (\<exists>query_idxs\<in>Q.
      query_rounds_index_list_hit s query_idxs rounds None)"
    by simp
next
  fix header t
  assume prefix:
    "Some (header, t) \<in>
      set_dist (execute verifier_composition_fri_prefix s)"
  obtain fr f_fl f_final as dg fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg, fl)"
    by (cases header) auto
  have future_t: "query_future_fresh t"
    by (rule verifier_composition_fri_prefix_preserves_query_future_fresh
        [OF future prefix])
  have counter_t: "PQueryCounter t = PQueryCounter s"
    using verifier_composition_fri_prefix_outcome[OF prefix[unfolded header_eq]]
    by simp
  show
    "wp_event (verifier_after_composition_fri header)
      (\<lambda>out. \<exists>query_idxs \<in> Q.
        query_rounds_index_list_hit s query_idxs rounds out) t \<le>
      nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
    by (rule wp_verifier_after_composition_fri_query_index_list_set_bound
        [OF future_t counter_t raw_bound subset])
qed

end

end
