(*  Title:      Stark/Soundness_FRI_First_Root_RO_Actual_Query_Product.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_Actual_Query_Product
  imports
    Soundness_FRI_First_Root_Actual_Agreement
    Staged_Security_Experiment_RO_Query_List_Actual_Path
begin

text \<open>
  A proof-only RO decomposition retains the actual first trace-FRI root and the
  hash state immediately after its domain-separated absorption.  Exact query
  products are then bounded for the agreement family selected by that realized
  prefix before averaging.  This layer does not use a choice-based prefix
  reconstruction and does not alter the protocol.
\<close>

context soundness
begin

definition ro_staged_first_trace_fri_root_prefix_program
  :: "'f staged_adversary \<Rightarrow>
      (('f \<times> 'f list \<times> 'f) \<times> 'f protocol_channel,
       'f protocol_channel) state_monad"
where
  "ro_staged_first_trace_fri_root_prefix_program A =
    do {
      fr \<leftarrow> trace_root_stage A;
      ro_record_staged_message fr;
      (case ceil_log clength of
        0 \<Rightarrow> do {
          prefix_state \<leftarrow> get;
          return ((fr, [], fr), prefix_state)
        }
      | Suc n \<Rightarrow> do {
          first_root \<leftarrow> trace_fri_root_stage A 0 [];
          ro_record_staged_message first_root;
          prefix_state \<leftarrow> get;
          return ((fr, [], first_root), prefix_state)
        })
    }"

definition ro_checked_staged_after_first_trace_fri_root_prefix_program
  :: "'f staged_adversary \<Rightarrow> ('f \<times> 'f list \<times> 'f) \<Rightarrow>
      ('f staged_proof_data, 'f protocol_channel) state_monad"
where
  "ro_checked_staged_after_first_trace_fri_root_prefix_program A prefix =
    (case prefix of (fr, trace_bs, first_root) \<Rightarrow>
      (case ceil_log clength of
        0 \<Rightarrow> do {
          trace_final \<leftarrow> trace_final_stage A [];
          ro_record_staged_message trace_final;
          as \<leftarrow> ro_staged_alpha_program (length spec);
          dg \<leftarrow> degree_stage A as;
          ro_record_staged_message dg;
          let composition_rounds = ceil_log (to_nat dg + 1);
          assert (composition_rounds \<le> ceil_log (maxDegree + 1));
          (composition_roots, composition_bs) \<leftarrow>
            ro_staged_composition_fri_program A dg 0 composition_rounds [];
          composition_final \<leftarrow> composition_final_stage A dg composition_bs;
          ro_record_staged_message composition_final;
          return
            \<lparr>staged_trace_root = fr,
             staged_trace_fri_roots = [],
             staged_trace_fri_challenges = [],
             staged_trace_final = trace_final,
             staged_alphas = as,
             staged_degree = dg,
             staged_composition_fri_roots = composition_roots,
             staged_composition_fri_challenges = composition_bs,
             staged_composition_final = composition_final,
             staged_query_chunks = []\<rparr>
        }
      | Suc n \<Rightarrow> do {
          b \<leftarrow> receive_trace_fri_challenge;
          (trace_roots, trace_bs') \<leftarrow>
            ro_staged_trace_fri_program A 1 n (trace_bs @ [b]);
          trace_final \<leftarrow> trace_final_stage A trace_bs';
          ro_record_staged_message trace_final;
          as \<leftarrow> ro_staged_alpha_program (length spec);
          dg \<leftarrow> degree_stage A as;
          ro_record_staged_message dg;
          let composition_rounds = ceil_log (to_nat dg + 1);
          assert (composition_rounds \<le> ceil_log (maxDegree + 1));
          (composition_roots, composition_bs) \<leftarrow>
            ro_staged_composition_fri_program A dg 0 composition_rounds [];
          composition_final \<leftarrow> composition_final_stage A dg composition_bs;
          ro_record_staged_message composition_final;
          return
            \<lparr>staged_trace_root = fr,
             staged_trace_fri_roots = first_root # trace_roots,
             staged_trace_fri_challenges = trace_bs',
             staged_trace_final = trace_final,
             staged_alphas = as,
             staged_degree = dg,
             staged_composition_fri_roots = composition_roots,
             staged_composition_fri_challenges = composition_bs,
             staged_composition_final = composition_final,
             staged_query_chunks = []\<rparr>
        }))"

definition ro_checked_staged_first_root_query_head_program
  :: "'f staged_adversary \<Rightarrow>
      ((('f \<times> 'f list \<times> 'f) \<times> 'f protocol_channel) \<times>
        'f staged_proof_data \<times> 'f protocol_channel,
       'f protocol_channel) state_monad"
where
  "ro_checked_staged_first_root_query_head_program A =
    do {
      prefix_with_state \<leftarrow> ro_staged_first_trace_fri_root_prefix_program A;
      data \<leftarrow>
        ro_checked_staged_after_first_trace_fri_root_prefix_program A
          (fst prefix_with_state);
      query_start \<leftarrow> get;
      return (prefix_with_state, data, query_start)
    }"

definition
  ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
  :: "'f staged_adversary \<Rightarrow>
      ((('f \<times> 'f list \<times> 'f) \<times> 'f protocol_channel) \<times>
        'f staged_proof_data \<times> 'f protocol_channel \<times>
        'f list \<times> 'f protocol_channel list,
       'f protocol_channel) state_monad"
where
  "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A =
    do {
      (prefix_with_state, data, query_start) \<leftarrow>
        ro_checked_staged_first_root_query_head_program A;
      (raws, query_states, query_chunks) \<leftarrow>
        ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds;
      return
        (prefix_with_state,
          data\<lparr>staged_query_chunks := query_chunks\<rparr>,
          query_start, raws, query_states)
    }"

lemma ro_checked_staged_transcript_program_first_root_prefix_decomposition:
  assumes nonempty: "0 < ceil_log clength"
  shows
    "ro_checked_staged_transcript_program A =
      ro_staged_first_trace_fri_root_prefix_program A \<bind>
        (\<lambda>prefix_with_state.
          ro_checked_staged_after_first_trace_fri_root_prefix_program A
              (fst prefix_with_state) \<bind>
            (\<lambda>data.
              ro_checked_staged_query_program A
                  (staged_trace_fri_roots data)
                  (staged_composition_fri_roots data)
                  0 rounds \<bind>
                (\<lambda>query_chunks.
                  return (data\<lparr>staged_query_chunks := query_chunks\<rparr>))))"
proof -
  obtain n where rounds_eq: "ceil_log clength = Suc n"
    using nonempty by (cases "ceil_log clength") auto
  show ?thesis
    unfolding ro_checked_staged_transcript_program_def
      ro_staged_first_trace_fri_root_prefix_program_def
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def
      rounds_eq
    by (simp add: sm_bind_assoc Let_def split_def sm_bind_get_ignore)
qed


lemma
  ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_projection:
  assumes nonempty: "0 < ceil_log clength"
  shows
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A \<bind>
        (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
          return (data, query_start, raws, query_states)) =
      ro_checked_staged_transcript_program_with_query_witnesses A"
proof -
  obtain n where rounds_eq: "ceil_log clength = Suc n"
    using nonempty by (cases "ceil_log clength") auto
  show ?thesis
    unfolding
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
      ro_checked_staged_first_root_query_head_program_def
      ro_checked_staged_transcript_program_with_query_witnesses_def
      ro_staged_first_trace_fri_root_prefix_program_def
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def
      ro_checked_staged_transcript_prefix_program_def
      rounds_eq
    by (simp add: sm_bind_assoc Let_def split_def sm_bind_get_ignore)
qed

lemma
  ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_projection_all_rounds:
  "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A \<bind>
      (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
        return (data, query_start, raws, query_states)) =
    ro_checked_staged_transcript_program_with_query_witnesses A"
proof (cases "ceil_log clength")
  case 0
  show ?thesis
    unfolding
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
      ro_checked_staged_first_root_query_head_program_def
      ro_checked_staged_transcript_program_with_query_witnesses_def
      ro_staged_first_trace_fri_root_prefix_program_def
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def
      ro_checked_staged_transcript_prefix_program_def
      0
    by (simp add: sm_bind_assoc Let_def split_def sm_bind_get_ignore)
next
  case (Suc n)
  show ?thesis
    unfolding
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
      ro_checked_staged_first_root_query_head_program_def
      ro_checked_staged_transcript_program_with_query_witnesses_def
      ro_staged_first_trace_fri_root_prefix_program_def
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def
      ro_checked_staged_transcript_prefix_program_def
      Suc
    by (simp add: sm_bind_assoc Let_def split_def sm_bind_get_ignore)
qed


lemma ro_checked_staged_first_root_query_head_program_state:
  assumes outcome:
    "Some ((prefix_with_state, data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  shows "t = query_start"
  using outcome
  unfolding ro_checked_staged_first_root_query_head_program_def
  by (auto elim!: set_dist_bindE)

definition
  ro_checked_staged_first_root_dependent_query_index_list_fresh_hit
where
  "ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (packed, attacker_state) \<Rightarrow>
        (case packed of
          (prefix_with_state, data, query_start, raws, query_states) \<Rightarrow>
            (case prefix_with_state of (prefix, prefix_state) \<Rightarrow>
              ro_query_witnesses_query_index_list_fresh_hit
                (Q prefix prefix_state)
                (Some ((raws, query_states, staged_query_chunks data),
                  attacker_state)))))"

lemma
  ro_checked_staged_first_root_dependent_query_index_list_fresh_hit_None[simp]:
  "\<not> ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q None"
  unfolding
    ro_checked_staged_first_root_dependent_query_index_list_fresh_hit_def
  by simp

lemma
  wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_dependent_fresh_bound:
  assumes subset:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute (ro_checked_staged_first_root_query_head_program A) s) \<Longrightarrow>
        Q prefix prefix_state \<subseteq> fri_query_index_list_space"
    and card_bound:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute (ro_checked_staged_first_root_query_head_program A) s) \<Longrightarrow>
        card (Q prefix prefix_state) \<le> N"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q)
      s \<le>
      nnreal N *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
  unfolding
    ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
proof (rule wp_event_bind_bound_by_cont)
  show
    "\<not> ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q None"
    by simp
next
  fix x t
  assume head:
    "Some (x, t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  obtain prefix prefix_state data query_start where x_eq:
    "x = ((prefix, prefix_state), data, query_start)"
    by (cases x) (auto split: prod.splits)
  have head':
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
    using head unfolding x_eq .
  have t_eq: "t = query_start"
    by (rule ro_checked_staged_first_root_query_head_program_state[OF head'])
  let ?Q = "Q prefix prefix_state"
  let ?R = "(nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
  have exact:
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds)
      (ro_query_witnesses_query_index_list_fresh_hit ?Q)
      query_start \<le>
      nnreal (card (query_index_raw_list_preimage ?Q)) *
        (1 / nnreal size) ^ rounds"
    by (rule
        wp_ro_checked_staged_query_program_with_witnesses_query_index_list_fresh_bound)
  have product:
    "nnreal (card (query_index_raw_list_preimage ?Q)) *
        (1 / nnreal size) ^ rounds \<le>
      nnreal (card ?Q) * ?R"
    by (rule query_index_raw_list_preimage_probability_bound[OF subset[OF head']])
  have local:
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds)
      (ro_query_witnesses_query_index_list_fresh_hit ?Q)
      query_start \<le>
      nnreal (card ?Q) * ?R"
    by (rule order_trans[OF exact product])
  have event_eq:
    "(\<lambda>out. case out of
      None \<Rightarrow>
        ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q None
    | Some (p, u) \<Rightarrow>
        ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q
          (Some
            ((((prefix, prefix_state),
                data\<lparr>staged_query_chunks := snd (snd p)\<rparr>,
                query_start, fst p, fst (snd p)), u)))) =
      ro_query_witnesses_query_index_list_fresh_hit ?Q"
    unfolding
      ro_checked_staged_first_root_dependent_query_index_list_fresh_hit_def
    by (rule ext) (auto split: option.splits prod.splits)
  have mapped:
    "wp_event
      (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks).
          return
            ((prefix, prefix_state),
              data\<lparr>staged_query_chunks := query_chunks\<rparr>,
              query_start, raws, query_states)))
      (ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q)
      query_start =
      wp_event
        (ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds)
        (ro_query_witnesses_query_index_list_fresh_hit ?Q)
        query_start"
    by (simp add: wp_event_bind_return_map split_def event_eq)
  have card_cast: "nnreal (card ?Q) \<le> nnreal N"
    using card_bound[OF head'] by simp
  have uniform: "nnreal (card ?Q) * ?R \<le> nnreal N * ?R"
    by (rule mult_right_mono[OF card_cast]) simp
  show
    "wp_event
      (case x of
        (prefix_with_state, data, query_start) \<Rightarrow>
          ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data)
              query_start 0 rounds \<bind>
            (\<lambda>(raws, query_states, query_chunks).
              return
                (prefix_with_state,
                  data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                  query_start, raws, query_states)))
      (ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q)
      t \<le> nnreal N * ?R"
    unfolding x_eq t_eq
  proof -
    have local':
      "wp_event
        (ro_checked_staged_query_program_with_witnesses A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)
            query_start 0 rounds \<bind>
          (\<lambda>(raws, query_states, query_chunks).
            return
              ((prefix, prefix_state),
                data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                query_start, raws, query_states)))
        (ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q)
        query_start \<le> nnreal (card ?Q) * ?R"
      unfolding mapped
      by (rule local)
    show
      "wp_event
        (case ((prefix, prefix_state), data, query_start) of
          (prefix_with_state, data, query_start) \<Rightarrow>
            ro_checked_staged_query_program_with_witnesses A
                (staged_trace_fri_roots data)
                (staged_composition_fri_roots data)
                query_start 0 rounds \<bind>
              (\<lambda>(raws, query_states, query_chunks).
                return
                  (prefix_with_state,
                    data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                    query_start, raws, query_states)))
        (ro_checked_staged_first_root_dependent_query_index_list_fresh_hit Q)
        query_start \<le> nnreal N * ?R"
      by (simp only: prod.case; rule order_trans[OF local' uniform])
  qed
qed


lemma
  wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_agreement_fresh_bound:
  assumes trace_low:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute (ro_checked_staged_first_root_query_head_program A) s) \<Longrightarrow>
        trace_table_low_degree
          (first_trace_fri_root_prefix_trace_table prefix prefix_state)"
    and first_low:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute (ro_checked_staged_first_root_query_head_program A) s) \<Longrightarrow>
        trace_table_low_degree
          (first_trace_fri_root_prefix_first_table prefix prefix_state)"
    and distinct:
      "\<And>prefix prefix_state data query_start t.
        Some (((prefix, prefix_state), data, query_start), t) \<in>
          set_dist
            (execute (ro_checked_staged_first_root_query_head_program A) s) \<Longrightarrow>
        first_trace_fri_root_prefix_trace_table prefix prefix_state \<noteq>
          first_trace_fri_root_prefix_first_table prefix prefix_state"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_checked_staged_first_root_dependent_query_index_list_fresh_hit
        first_trace_fri_root_prefix_base_agreement_query_lists)
      s \<le>
      nnreal (clength ^ rounds) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof (rule
    wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_dependent_fresh_bound)
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  show
    "first_trace_fri_root_prefix_base_agreement_query_lists
        prefix prefix_state
      \<subseteq> fri_query_index_list_space"
    by (rule first_trace_fri_root_prefix_base_agreement_query_lists_subset)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  show
    "card
        (first_trace_fri_root_prefix_base_agreement_query_lists
          prefix prefix_state)
      \<le> clength ^ rounds"
    by (rule
        first_trace_fri_root_prefix_base_agreement_query_lists_card_bound[
          OF trace_low[OF head] first_low[OF head] distinct[OF head]])
qed

end
end
