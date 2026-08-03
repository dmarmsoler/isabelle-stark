(*  Title:      Stark/Soundness_FRI_Query_Index_Staged_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Query_Index_Staged_Bounds
  imports Soundness_FRI_Sampled_Interface
begin

text \<open>
  Staged query-index accounting for FRI query-list events.

  The verifier-local exact query-list bounds still assume query freshness of
  the transferred verifier state.  This layer charges accepted FRI query-list
  hits to the checked staged transcript query-index target event, using only
  the query indices actually derived by the verifier.
\<close>

lemma pair_second_set_cover_split:
  assumes "(x, y) \<in> P"
  shows "y \<in> B \<or> (x, y) \<in> P \<inter> (UNIV \<times> (- B))"
proof (cases "y \<in> B")
  case True
  then show ?thesis ..
next
  case False
  then have "(x, y) \<in> P \<inter> (UNIV \<times> (- B))"
    using assms by simp
  then show ?thesis ..
qed

context soundness
begin

lemma accepted_fri_opening_transcript_query_headerE:
  assumes
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final query_idxs
      trace_round_layers composition_round_layers"
  obtains fr as query_state where
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final (PTranscript query_state)"
    "PState query_state =
      verifier_header_state s fr trace_roots trace_final as dg
        composition_roots composition_final"
    "verifier_query_indices_derived s out
      (verifier_header_state s fr trace_roots trace_final as dg
        composition_roots composition_final)
      (PTranscript query_state) trace_roots composition_roots query_idxs"
proof -
  show ?thesis
    using assms
    unfolding accepted_fri_opening_transcript_def
    apply (elim exE conjE)
    apply (rule that)
    by (auto intro: Channel_Core.protocol_channel.select_convs(1))
qed

lemma accepted_fri_opening_transcript_imp_staged_query_index_set_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and openings:
      "accepted_fri_opening_transcript
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) trace_roots trace_bs trace_final dg
        composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and query_in: "query_idxs \<in> Q"
  shows "staged_security_with_data_query_index_set_hit
    (query_index_list_entries Q) (Some ((data, result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from accepted_fri_opening_transcript_query_headerE[OF openings]
  obtain fr as query_state where
    header:
      "verifier_header_transcript ?s fr trace_roots trace_final as dg
        composition_roots composition_final (PTranscript query_state)"
    and query_state_hash:
      "PState query_state =
        verifier_header_state ?s fr trace_roots trace_final as dg
          composition_roots composition_final"
    and derived:
      "verifier_query_indices_derived ?s (Some (result, final_state))
        (verifier_header_state ?s fr trace_roots trace_final as dg
          composition_roots composition_final)
        (PTranscript query_state) trace_roots composition_roots query_idxs"
    by blast
  have staged_header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
	  have header_eq:
	    "fr = staged_trace_root data \<and>
	     trace_roots = staged_trace_fri_roots data \<and>
	     trace_final = staged_trace_final data \<and>
	     as = staged_alphas data \<and>
	     dg = staged_degree data \<and>
	     composition_roots = staged_composition_fri_roots data \<and>
	     composition_final = staged_composition_final data \<and>
	     PTranscript query_state = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  have query_start_eq:
    "verifier_header_state ?s fr trace_roots trace_final as dg
      composition_roots composition_final =
     staged_query_start_hash data"
	    using query_state_hash header_eq
	    unfolding staged_query_start_hash_def
	      staged_composition_fri_start_hash_def
	      staged_trace_fri_start_hash_def
	      verifier_header_state_def verifier_header_messages_def
	      verifier_state_from_adversary_def
	    by simp
  have query_counter: "PQueryCounter ?s = 0"
    unfolding verifier_state_from_adversary_def by simp
  from verifier_query_indices_derivedE[OF derived]
  obtain result' final_state' raw_idxs query_chunks trailing where
    out_derived: "Some (result, final_state) = Some (result', final_state')"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and concat_eq:
      "List.concat query_chunks @ trailing = PTranscript query_state"
    and round_chunks:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)"
    and lookups':
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter ?s + i)
            (state_after_query_chunks
              (verifier_header_state ?s fr trace_roots trace_final as dg
                composition_roots composition_final)
              query_chunks i)) =
        Some (raw_idxs ! i)"
    by metis
  have final_state'_eq: "final_state' = final_state"
    using out_derived by simp
  have lookups:
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter ?s + i)
          (state_after_query_chunks
            (verifier_header_state ?s fr trace_roots trace_final as dg
              composition_roots composition_final)
            query_chunks i)) =
      Some (raw_idxs ! i)"
    using lookups' final_state'_eq by simp
  have len_query: "length query_idxs = rounds"
    using len_raw query_idxs_eq by simp
  have parser_chunk_len:
    "\<And>i. i < rounds \<Longrightarrow>
      length (query_chunks ! i) =
        verifier_query_round_transcript_length (query_idxs ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    show
      "length (query_chunks ! i) =
        verifier_query_round_transcript_length (query_idxs ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)"
      using verifier_query_round_chunk_length[OF round_chunks[OF i_bound]]
        header_eq
      by simp
  qed
  have concat_staged:
    "List.concat query_chunks @ trailing =
      List.concat (staged_query_chunks data)"
    using concat_eq header_eq by simp
  have chunks_eq: "query_chunks = staged_query_chunks data"
    using selected_query_chunks_eq_staged
      [OF builder len_query len_chunks concat_staged parser_chunk_len]
    by simp
  from rounds_positive obtain i where i_bound: "i < rounds"
    by auto
  have idx_in: "query_idxs ! i \<in> query_index_list_entries Q"
    using query_in i_bound len_query unfolding query_index_list_entries_def
    by (auto intro: nth_mem)
  have lookup:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    using lookups[OF i_bound] query_counter query_start_eq chunks_eq
    by simp
  have raw_hit:
    "index (to_nat (raw_idxs ! i)) \<in> query_index_list_entries Q"
    using idx_in query_idxs_eq i_bound len_raw by simp
  show ?thesis
    unfolding staged_security_with_data_query_index_set_hit_def
    using i_bound lookup raw_hit by auto
qed

lemma checked_staged_security_trace_fri_query_index_list_set_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state \<le>
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
	proof -
	  let ?B = "query_index_list_entries Q"
	  let ?projected =
	    "\<lambda>out. case out of None \<Rightarrow>
	        staged_security_with_data_query_index_set_hit ?B None
	      | Some (((data, _), result), t) \<Rightarrow>
	        staged_security_with_data_query_index_set_hit ?B
	          (Some ((data, result), t))"
	  have event_le:
	    "wp_event (checked_staged_security_experiment_with_data_state A)
	      (staged_security_with_data_state_verifier_event
	        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
	      adversary_initial_state \<le>
	    wp_event (checked_staged_security_experiment_with_data_state A)
	      ?projected adversary_initial_state"
	  proof (rule wp_event_mono_on_support)
	    fix out
	    assume out_support:
	      "out \<in>
	        set_dist
	          (execute (checked_staged_security_experiment_with_data_state A)
	            adversary_initial_state)"
	    assume hit:
	      "staged_security_with_data_state_verifier_event
	        (\<lambda>s. trace_fri_query_index_list_set_hit s Q) out"
	    show "?projected out"
	    proof (cases out)
	      case None
	      then show ?thesis
	        using hit
	        unfolding staged_security_with_data_state_verifier_event_def
	          staged_security_with_data_query_index_set_hit_def
	        by simp
	    next
	      case (Some pair)
	      then obtain data attacker_state result final_state where out_eq:
	        "out = Some (((data, attacker_state), result), final_state)"
	        by (cases pair) (auto split: prod.splits)
	      let ?s =
	        "verifier_state_from_adversary attacker_state
	          (staged_proof_transcript data)"
	      have builder:
	        "Some (data, attacker_state) \<in>
	          set_dist
	            (execute (checked_staged_transcript_program A)
	              adversary_initial_state)"
	        using out_support
	        unfolding out_eq checked_staged_security_experiment_with_data_state_def
	        by (auto elim!: set_dist_bindE)
	      from hit out_eq have trace_hit:
	        "trace_fri_query_index_list_set_hit ?s Q
	          (Some (result, final_state))"
	        unfolding staged_security_with_data_state_verifier_event_def by simp
	      from trace_hit obtain trace_roots trace_bs trace_final dg
	          composition_roots composition_bs composition_final query_idxs
	          trace_round_layers composition_round_layers where
	        fri:
	          "accepted_fri_opening_transcript ?s (Some (result, final_state))
	            trace_roots trace_bs trace_final dg composition_roots
	            composition_bs composition_final query_idxs trace_round_layers
	            composition_round_layers"
	        and query_in: "query_idxs \<in> Q"
	        unfolding trace_fri_query_index_list_set_hit_def by blast
	      have staged_hit:
	        "staged_security_with_data_query_index_set_hit
	          (query_index_list_entries Q)
	          (Some ((data, result), final_state))"
	        by (rule
	            accepted_fri_opening_transcript_imp_staged_query_index_set_hit
	            [OF wf controlled builder fri query_in])
	      show ?thesis
	        unfolding out_eq using staged_hit by simp
	    qed
	  qed
	  also have
	    "wp_event (checked_staged_security_experiment_with_data_state A)
	      ?projected adversary_initial_state =
	    wp_event (checked_staged_security_experiment_with_data A)
	      (staged_security_with_data_query_index_set_hit ?B)
	      adversary_initial_state"
	    using checked_staged_security_experiment_with_data_event_from_data_state
	      [of A "staged_security_with_data_query_index_set_hit ?B"]
	    by simp
	  also have "... \<le>
	      staged_phase_target_error
	        (query_index_raw_preimage (query_index_list_entries Q))
	        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
	    by (rule checked_staged_security_with_data_query_index_set_hit_bound
	        [OF wf controlled])
	  finally show ?thesis .
	qed

lemma checked_staged_security_composition_fri_query_index_list_set_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state \<le>
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
	proof -
	  let ?B = "query_index_list_entries Q"
	  let ?projected =
	    "\<lambda>out. case out of None \<Rightarrow>
	        staged_security_with_data_query_index_set_hit ?B None
	      | Some (((data, _), result), t) \<Rightarrow>
	        staged_security_with_data_query_index_set_hit ?B
	          (Some ((data, result), t))"
	  have event_le:
	    "wp_event (checked_staged_security_experiment_with_data_state A)
	      (staged_security_with_data_state_verifier_event
	        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
	      adversary_initial_state \<le>
	    wp_event (checked_staged_security_experiment_with_data_state A)
	      ?projected adversary_initial_state"
	  proof (rule wp_event_mono_on_support)
	    fix out
	    assume out_support:
	      "out \<in>
	        set_dist
	          (execute (checked_staged_security_experiment_with_data_state A)
	            adversary_initial_state)"
	    assume hit:
	      "staged_security_with_data_state_verifier_event
	        (\<lambda>s. composition_fri_query_index_list_set_hit s Q) out"
	    show "?projected out"
	    proof (cases out)
	      case None
	      then show ?thesis
	        using hit
	        unfolding staged_security_with_data_state_verifier_event_def
	          staged_security_with_data_query_index_set_hit_def
	        by simp
	    next
	      case (Some pair)
	      then obtain data attacker_state result final_state where out_eq:
	        "out = Some (((data, attacker_state), result), final_state)"
	        by (cases pair) (auto split: prod.splits)
	      let ?s =
	        "verifier_state_from_adversary attacker_state
	          (staged_proof_transcript data)"
	      have builder:
	        "Some (data, attacker_state) \<in>
	          set_dist
	            (execute (checked_staged_transcript_program A)
	              adversary_initial_state)"
	        using out_support
	        unfolding out_eq checked_staged_security_experiment_with_data_state_def
	        by (auto elim!: set_dist_bindE)
	      from hit out_eq have composition_hit:
	        "composition_fri_query_index_list_set_hit ?s Q
	          (Some (result, final_state))"
	        unfolding staged_security_with_data_state_verifier_event_def by simp
	      from composition_hit obtain trace_roots trace_bs trace_final dg
	          composition_roots composition_bs composition_final query_idxs
	          trace_round_layers composition_round_layers where
	        fri:
	          "accepted_fri_opening_transcript ?s (Some (result, final_state))
	            trace_roots trace_bs trace_final dg composition_roots
	            composition_bs composition_final query_idxs trace_round_layers
	            composition_round_layers"
	        and query_in: "query_idxs \<in> Q"
	        unfolding composition_fri_query_index_list_set_hit_def by blast
	      have staged_hit:
	        "staged_security_with_data_query_index_set_hit
	          (query_index_list_entries Q)
	          (Some ((data, result), final_state))"
	        apply (rule
	            accepted_fri_opening_transcript_imp_staged_query_index_set_hit
	            [OF wf controlled builder fri query_in])
	        .
	      show ?thesis
	        unfolding out_eq using staged_hit by simp
	    qed
	  qed
	  also have
	    "wp_event (checked_staged_security_experiment_with_data_state A)
	      ?projected adversary_initial_state =
	    wp_event (checked_staged_security_experiment_with_data A)
	      (staged_security_with_data_query_index_set_hit ?B)
	      adversary_initial_state"
	    using checked_staged_security_experiment_with_data_event_from_data_state
	      [of A "staged_security_with_data_query_index_set_hit ?B"]
	    by simp
	  also have "... \<le>
	      staged_phase_target_error
	        (query_index_raw_preimage (query_index_list_entries Q))
	        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
	    by (rule checked_staged_security_with_data_query_index_set_hit_bound
	        [OF wf controlled])
	  finally show ?thesis .
	qed

lemma checked_staged_security_trace_fri_query_challenge_pair_set_hit_bound_from_query_projection:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and projection: "fst ` P \<subseteq> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule order_trans)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          trace_fri_query_challenge_pair_set_hit_imp_query_index_list_set_hit
            [OF _ projection]
        split: option.splits prod.splits)
next
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state
      \<le> staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    apply (rule checked_staged_security_trace_fri_query_index_list_set_hit_bound
        [OF wf controlled]) .
qed

lemma checked_staged_security_composition_fri_query_challenge_pair_set_hit_bound_from_query_projection:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and projection: "\<And>dg. fst ` P dg \<subseteq> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule order_trans)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_fri_query_challenge_pair_set_hit_imp_query_index_list_set_hit
            [OF _ projection]
        split: option.splits prod.splits)
next
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state
      \<le> staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule
        checked_staged_security_composition_fri_query_index_list_set_hit_bound
        [OF wf controlled])
qed

lemma checked_staged_security_trace_fri_sampled_query_pair_set_hit_bound_from_query_projection:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and projection:
      "\<And>trace_table roots final round_layers layers.
        fst ` R trace_table roots final round_layers layers \<subseteq> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_query_pair_set_hit R s))
      adversary_initial_state \<le>
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule order_trans)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_query_pair_set_hit R s))
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          trace_fri_sampled_query_pair_set_hit_imp_query_index_list_set_hit
            [OF _ projection]
        split: option.splits prod.splits)
next
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s Q))
      adversary_initial_state
      \<le> staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule checked_staged_security_trace_fri_query_index_list_set_hit_bound
        [OF wf controlled])
qed

lemma checked_staged_security_composition_fri_sampled_query_pair_set_hit_bound_from_query_projection:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and projection:
      "\<And>fri_dg composition_table roots final round_layers layers.
        fst ` R fri_dg composition_table roots final round_layers layers
          \<subseteq> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_query_pair_set_hit R s))
      adversary_initial_state \<le>
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof (rule order_trans)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_query_pair_set_hit R s))
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_fri_sampled_query_pair_set_hit_imp_query_index_list_set_hit
            [OF _ projection]
        split: option.splits prod.splits)
next
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_index_list_set_hit s Q))
      adversary_initial_state
      \<le> staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
    by (rule
        checked_staged_security_composition_fri_query_index_list_set_hit_bound
        [OF wf controlled])
qed

lemma trace_fri_query_challenge_pair_set_hit_split_by_pair_cover:
  assumes hit: "trace_fri_query_challenge_pair_set_hit s P out"
  shows
    "trace_fri_query_challenge_pair_set_hit s
      (P \<inter> (UNIV \<times> B)) out \<or>
     trace_fri_query_challenge_pair_set_hit s
      (P \<inter> (UNIV \<times> (- B))) out"
proof -
  show ?thesis
    using hit
    unfolding trace_fri_query_challenge_pair_set_hit_def
    apply (elim exE conjE)
    apply (subgoal_tac
      "(fri_query_idxs, trace_bs) \<in> P \<inter> (UNIV \<times> B) \<or>
       (fri_query_idxs, trace_bs) \<in> P \<inter> (UNIV \<times> (- B))")
     apply (erule disjE)
      apply (rule disjI1)
      apply (intro exI conjI)
       apply assumption
      apply assumption
     apply (rule disjI2)
     apply (intro exI conjI)
      apply assumption
     apply assumption
    by simp
qed

lemma composition_fri_query_challenge_pair_set_hit_split_by_pair_cover:
  assumes hit: "composition_fri_query_challenge_pair_set_hit s P out"
  shows
    "composition_fri_query_challenge_pair_set_hit s
      (\<lambda>dg. P dg \<inter> (UNIV \<times> B dg)) out \<or>
     composition_fri_query_challenge_pair_set_hit s
      (\<lambda>dg. P dg \<inter> (UNIV \<times> (- B dg))) out"
proof -
  show ?thesis
    using hit
    unfolding composition_fri_query_challenge_pair_set_hit_def
    apply (elim exE conjE)
    apply (subgoal_tac
      "(fri_query_idxs, composition_bs) \<in> P fri_dg \<inter> (UNIV \<times> B fri_dg) \<or>
       (fri_query_idxs, composition_bs) \<in>
        P fri_dg \<inter> (UNIV \<times> (- B fri_dg))")
     apply (erule disjE)
      apply (rule disjI1)
      apply (intro exI conjI)
       apply assumption
      apply assumption
     apply (rule disjI2)
     apply (intro exI conjI)
      apply assumption
     apply assumption
    by auto
qed

lemma checked_staged_security_trace_fri_query_challenge_pair_set_hit_bound_from_challenge_cover_and_query_projection:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and projection:
      "fst ` (P \<inter> (UNIV \<times> (- B))) \<subseteq> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget) +
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  let ?Inside = "P \<inter> (UNIV \<times> B)"
  let ?Outside = "P \<inter> (UNIV \<times> (- B))"
  let ?challenge_event =
    "staged_security_with_data_state_verifier_event
      (\<lambda>s. trace_fri_challenge_list_set_hit s B)"
  let ?inside_event =
    "staged_security_with_data_state_verifier_event
      (\<lambda>s. trace_fri_query_challenge_pair_set_hit s ?Inside)"
  let ?outside_event =
    "staged_security_with_data_state_verifier_event
      (\<lambda>s. trace_fri_query_challenge_pair_set_hit s ?Outside)"
  let ?hbudget =
    "hash_relation_budget_value (card B * ceil_log clength)
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
  let ?qbudget =
    "staged_phase_target_error
      (query_index_raw_preimage (query_index_list_entries Q))
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
  have split:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
	     wp_event (checked_staged_security_experiment_with_data_state A)
	      (\<lambda>out.
	        ?inside_event out \<or> ?outside_event out)
	      adversary_initial_state"
		  proof (rule wp_event_mono_on_support)
		    fix out
	    assume hit:
	      "staged_security_with_data_state_verifier_event
	        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P) out"
		    then show
		      "?inside_event out \<or> ?outside_event out"
		      unfolding staged_security_with_data_state_verifier_event_def
			      by (auto
			          dest: trace_fri_query_challenge_pair_set_hit_split_by_pair_cover
			          split: option.splits prod.splits)
		  qed
  have union_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out. ?inside_event out \<or> ?outside_event out)
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?inside_event adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?outside_event adversary_initial_state"
    by (rule wp_event_union_bound)
  have split_union_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?inside_event adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?outside_event adversary_initial_state"
    apply (rule order_trans)
     apply (rule split)
    apply (rule union_bound)
    done
  have sum_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      ?inside_event adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?outside_event adversary_initial_state \<le> (F + ?hbudget) + ?qbudget"
  proof -
    have challenge_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        ?challenge_event adversary_initial_state \<le> F + ?hbudget"
      by (rule checked_staged_security_trace_fri_challenge_list_set_hit_bound
          [OF wf controlled finite_B fresh_bound])
    have inside_projection: "snd ` ?Inside \<subseteq> B"
      by force
    have inside_to_challenge:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        ?inside_event adversary_initial_state \<le>
       wp_event (checked_staged_security_experiment_with_data_state A)
        ?challenge_event adversary_initial_state"
      by (rule wp_event_mono_on_support)
        (auto simp: staged_security_with_data_state_verifier_event_def
          intro:
            trace_fri_query_challenge_pair_set_hit_imp_challenge_list_set_hit
              [OF _ inside_projection]
          split: option.splits prod.splits)
    have inside_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        ?inside_event adversary_initial_state \<le> F + ?hbudget"
      apply (rule order_trans)
       apply (rule inside_to_challenge)
      apply (rule challenge_bound)
      done
    have outside_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        ?outside_event adversary_initial_state \<le> ?qbudget"
      by (rule
          checked_staged_security_trace_fri_query_challenge_pair_set_hit_bound_from_query_projection
          [OF wf controlled projection])
    show ?thesis
      by (rule add_mono[OF inside_bound outside_bound])
  qed
  show ?thesis
    using order_trans[OF split_union_bound sum_bound]
    by (simp add: add.assoc)
qed

lemma checked_staged_security_composition_fri_query_challenge_pair_set_hit_bound_from_challenge_cover_and_query_projection:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and projection:
      "\<And>dg. fst ` (P dg \<inter> (UNIV \<times> (- B dg))) \<subseteq> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  let ?Inside = "\<lambda>dg. P dg \<inter> (UNIV \<times> B dg)"
  let ?Outside = "\<lambda>dg. P dg \<inter> (UNIV \<times> (- B dg))"
  let ?challenge_event =
    "staged_security_with_data_state_verifier_event
      (\<lambda>s. composition_fri_challenge_list_set_hit s B)"
  let ?inside_event =
    "staged_security_with_data_state_verifier_event
      (\<lambda>s. composition_fri_query_challenge_pair_set_hit s ?Inside)"
  let ?outside_event =
    "staged_security_with_data_state_verifier_event
      (\<lambda>s. composition_fri_query_challenge_pair_set_hit s ?Outside)"
  let ?hbudget =
    "hash_relation_budget_value
      (\<Sum>dg \<in> (UNIV :: 'f set).
        card (B dg) * ceil_log (maxDegree + 1))
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
  let ?qbudget =
    "staged_phase_target_error
      (query_index_raw_preimage (query_index_list_entries Q))
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
  have split:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
	     wp_event (checked_staged_security_experiment_with_data_state A)
	      (\<lambda>out.
	        ?inside_event out \<or> ?outside_event out)
	      adversary_initial_state"
		  proof (rule wp_event_mono_on_support)
		    fix out
	    assume hit:
	      "staged_security_with_data_state_verifier_event
	        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P) out"
		    then show
		      "?inside_event out \<or> ?outside_event out"
		      unfolding staged_security_with_data_state_verifier_event_def
			      by (auto
			          dest: composition_fri_query_challenge_pair_set_hit_split_by_pair_cover
			          split: option.splits prod.splits)
		  qed
  have union_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out. ?inside_event out \<or> ?outside_event out)
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?inside_event adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?outside_event adversary_initial_state"
    by (rule wp_event_union_bound)
  have split_union_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?inside_event adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?outside_event adversary_initial_state"
    apply (rule order_trans)
     apply (rule split)
    apply (rule union_bound)
    done
  have sum_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      ?inside_event adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?outside_event adversary_initial_state \<le> (F + ?hbudget) + ?qbudget"
  proof -
    have challenge_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        ?challenge_event adversary_initial_state \<le> F + ?hbudget"
      by (rule
          checked_staged_security_composition_fri_challenge_list_set_hit_bound
          [OF wf controlled finite_B fresh_bound])
    have inside_projection: "\<And>dg. snd ` ?Inside dg \<subseteq> B dg"
      by force
    have inside_to_challenge:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        ?inside_event adversary_initial_state \<le>
       wp_event (checked_staged_security_experiment_with_data_state A)
        ?challenge_event adversary_initial_state"
      by (rule wp_event_mono_on_support)
        (auto simp: staged_security_with_data_state_verifier_event_def
          intro:
            composition_fri_query_challenge_pair_set_hit_imp_challenge_list_set_hit
              [OF _ inside_projection]
          split: option.splits prod.splits)
    have inside_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        ?inside_event adversary_initial_state \<le> F + ?hbudget"
      apply (rule order_trans)
       apply (rule inside_to_challenge)
      apply (rule challenge_bound)
      done
    have outside_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        ?outside_event adversary_initial_state \<le> ?qbudget"
      by (rule
          checked_staged_security_composition_fri_query_challenge_pair_set_hit_bound_from_query_projection
          [OF wf controlled projection])
    show ?thesis
      by (rule add_mono[OF inside_bound outside_bound])
  qed
  show ?thesis
    using order_trans[OF split_union_bound sum_bound]
    by (simp add: add.assoc)
qed

lemma checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_challenge_cover_and_query_projection:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and projection:
      "fst `
        ((trace_fri_sampled_query_bad_pair_union \<inter>
          (fri_query_index_list_space \<times> UNIV)) \<inter>
          (UNIV \<times> (- B))) \<subseteq> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget) +
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  let ?P =
    "trace_fri_sampled_query_bad_pair_union \<inter>
      (fri_query_index_list_space \<times> UNIV)"
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s ?P))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          trace_fri_sampled_query_bad_candidate_imp_restricted_query_challenge_pair_union_hit
        split: option.splits prod.splits)
  also have "... \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_query_challenge_pair_set_hit_bound_from_challenge_cover_and_query_projection
        [OF wf controlled finite_B fresh_bound projection])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_challenge_cover_and_query_projection:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and projection:
      "\<And>dg. fst `
        ((composition_fri_sampled_query_bad_pair_union dg \<inter>
          (fri_query_index_list_space \<times> UNIV)) \<inter>
          (UNIV \<times> (- B dg))) \<subseteq> Q"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  let ?P =
    "\<lambda>dg. composition_fri_sampled_query_bad_pair_union dg \<inter>
      (fri_query_index_list_space \<times> UNIV)"
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s ?P))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_fri_sampled_query_bad_candidate_imp_restricted_query_challenge_pair_union_hit
        split: option.splits prod.splits)
  also have "... \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      staged_phase_target_error
        (query_index_raw_preimage (query_index_list_entries Q))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule
        checked_staged_security_composition_fri_query_challenge_pair_set_hit_bound_from_challenge_cover_and_query_projection
        [OF wf controlled finite_B fresh_bound projection])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_generic_cover:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
    "generic_fri_sampled_query_finite_cover trace_table_low_degree
      (Not \<circ> trace_table_low_degree) (clength - 1) B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets + staged_challenge_query_budget)"
proof -
  have finite_B: "finite B"
    by (rule generic_fri_sampled_query_finite_coverD(1)[OF cover])
  have projection:
    "snd `
      (trace_fri_sampled_query_bad_pair_union \<inter>
        (fri_query_index_list_space \<times> UNIV)) \<subseteq> B"
    using generic_fri_sampled_query_finite_coverD(2)[OF cover]
    unfolding trace_fri_sampled_query_bad_pair_union_def by simp
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_set_hit s B))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          trace_fri_query_challenge_pair_set_hit_imp_challenge_list_set_hit
            [OF trace_fri_sampled_query_bad_candidate_imp_restricted_query_challenge_pair_union_hit
              projection]
        split: option.splits prod.splits)
  also have "... \<le>
      F +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule checked_staged_security_trace_fri_challenge_list_set_hit_bound
        [OF wf controlled finite_B fresh_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_generic_cover:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
    "\<And>dg. generic_fri_sampled_query_finite_cover
      (composition_table_low_degree (to_nat dg))
      (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg) (B dg)"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  have finite_B: "\<And>dg. finite (B dg)"
    by (rule generic_fri_sampled_query_finite_coverD(1)[OF cover])
  have projection:
    "\<And>dg. snd `
      (composition_fri_sampled_query_bad_pair_union dg \<inter>
        (fri_query_index_list_space \<times> UNIV)) \<subseteq> B dg"
  proof -
    fix dg
    show "snd `
      (composition_fri_sampled_query_bad_pair_union dg \<inter>
        (fri_query_index_list_space \<times> UNIV)) \<subseteq> B dg"
      using generic_fri_sampled_query_finite_coverD(2)[OF cover[of dg]]
      unfolding composition_fri_sampled_query_bad_pair_union_def by simp
  qed
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_set_hit s B))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_fri_query_challenge_pair_set_hit_imp_challenge_list_set_hit
            [OF composition_fri_sampled_query_bad_candidate_imp_restricted_query_challenge_pair_union_hit
              projection]
        split: option.splits prod.splits)
  also have "... \<le>
      F +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule checked_staged_security_composition_fri_challenge_list_set_hit_bound
        [OF wf controlled finite_B fresh_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_sampled_layer_chain_bound_from_sampled_query:
  assumes sampled_query:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> R"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state \<le> R"
proof -
  have missing:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_missing_canonical_sampled_layer_chain)
      adversary_initial_state \<le> 0"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
	    show "\<And>s. \<not> trace_fri_sampled_missing_canonical_sampled_layer_chain s None"
	      unfolding trace_fri_sampled_missing_canonical_sampled_layer_chain_def
	        trace_fri_bad_with_sampled_layer_chain_def
	        accepted_fri_opening_transcript_def
	        trace_fri_partial_candidate_opening_evidence_def
	        trace_fri_partial_candidate_evidence_def
	      by blast
  next
    fix data attacker_state
    assume
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
        (trace_fri_sampled_missing_canonical_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> 0"
      by (rule wp_trace_fri_missing_canonical_sampled_zero)
  qed
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_with_data_state_verifier_event
          trace_fri_sampled_query_bad_candidate out \<or>
        staged_security_with_data_state_verifier_event
          trace_fri_sampled_missing_canonical_sampled_layer_chain out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        trace_fri_sampled_query_bad_candidate_iff_canonical
        dest: trace_fri_sampled_layer_chain_canonical_or_missing
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_sampled_query_bad_candidate)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_sampled_missing_canonical_sampled_layer_chain)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> R + 0"
    by (rule add_mono[OF sampled_query missing])
  finally show ?thesis
    by simp
qed

lemma checked_staged_security_composition_fri_verifier_tied_sampled_layer_chain_bound_from_sampled_query:
  assumes sampled_query:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> R"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state \<le> R"
proof -
  have missing:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_missing_canonical_sampled_layer_chain)
      adversary_initial_state \<le> 0"
  proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    show
	      "\<And>s. \<not> composition_fri_sampled_missing_canonical_sampled_layer_chain
	        s None"
	      unfolding composition_fri_sampled_missing_canonical_sampled_layer_chain_def
	        composition_fri_bad_with_sampled_layer_chain_def
	        accepted_fri_opening_transcript_def
	        composition_fri_partial_candidate_opening_evidence_def
	        composition_fri_partial_candidate_evidence_def
	      by blast
  next
    fix data attacker_state
    assume
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
        (composition_fri_sampled_missing_canonical_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> 0"
      by (rule wp_composition_fri_missing_canonical_sampled_zero)
  qed
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_with_data_state_verifier_event
          composition_fri_sampled_query_bad_candidate out \<or>
        staged_security_with_data_state_verifier_event
          composition_fri_sampled_missing_canonical_sampled_layer_chain out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        composition_fri_sampled_query_bad_candidate_iff_canonical
        dest!: composition_fri_verifier_tied_sampled_layer_chain_imp_sampled_layer_chain
        dest: composition_fri_sampled_layer_chain_canonical_or_missing
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_sampled_query_bad_candidate)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_sampled_missing_canonical_sampled_layer_chain)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> R + 0"
    by (rule add_mono[OF sampled_query missing])
  finally show ?thesis
    by simp
qed

lemma checked_staged_security_trace_fri_empty_header_bound_from_sampled_query_conflict_and_zero:
  assumes sampled_query:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> R"
    and conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
    and zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> R + (C + Z)"
proof (rule checked_staged_security_trace_fri_empty_header_bound_from_sampled_and_missing)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state \<le> R"
    by (rule
        checked_staged_security_trace_fri_sampled_layer_chain_bound_from_sampled_query
        [OF sampled_query])
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have obstruction:
    "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction ?s) ?s \<le> C + Z"
    by (rule
        wp_trace_fri_sampled_layer_assignment_obstruction_bound_from_conflict_and_zero)
      (rule conflict_bound[OF support], rule zero_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain ?s) ?s \<le> C + Z"
	    by (rule wp_trace_fri_reachable_missing_sampled_bound_from_assignment_obstruction)
	      (rule obstruction)
qed

lemma wp_composition_fri_verifier_tied_missing_sampled_layer_chain_bound_from_residual_gaps:
  assumes slot_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s) s
      \<le> Slot"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s
        \<le> Merkle"
    and missing_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s) s
        \<le> Missing"
    and next_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap s) s
        \<le> Next"
    and successor_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap s) s
        \<le> Successor"
    and final_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap s) s
        \<le> Final"
    and zero_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_zero_round_final_obstruction s) s
        \<le> Zero"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_missing_sampled_layer_chain s) s
      \<le>
      (((Merkle + Missing) + Next + Successor + Final + Merkle) +
        Slot + Zero)"
proof -
  have conflict:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s
      \<le> ((Merkle + Missing) + Next + Successor + Final + Merkle) + Slot"
    by (rule
        wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_slot_recorded_chunk_gap_and_residuals
        [OF slot_bound merkle_bound missing_bound next_bound successor_bound
          final_bound])
  have obstruction:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_layer_assignment_obstruction s) s
      \<le>
      (((Merkle + Missing) + Next + Successor + Final + Merkle) +
        Slot + Zero)"
    by (rule
        wp_composition_fri_verifier_tied_assignment_obstruction_bound_from_conflict_and_zero)
      (rule conflict, rule zero_bound)
  show ?thesis
    by (rule
        wp_composition_fri_verifier_tied_missing_sampled_bound_from_assignment_obstruction)
      (rule obstruction)
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_sampled_query_and_residual_gaps:
  assumes sampled_query:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> R"
    and slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Slot"
    and merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Merkle"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_recorded_base_chunk_auth_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Missing"
    and next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Next"
    and successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Successor"
    and final_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Final"
    and zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Zero"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      R + (((Merkle + Missing) + Next + Successor + Final + Merkle) +
        Slot + Zero)"
	proof -
	  have sampled:
	    "wp_event (checked_staged_security_experiment_with_data_state A)
	      (staged_security_with_data_state_verifier_event
	        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
	      adversary_initial_state \<le> R"
	    by (rule
	        checked_staged_security_composition_fri_verifier_tied_sampled_layer_chain_bound_from_sampled_query
	        [OF sampled_query])
	  have missing:
	    "\<And>data attacker_state.
	      Some (data, attacker_state) \<in>
	        set_dist (execute (checked_staged_transcript_program A)
	          adversary_initial_state) \<Longrightarrow>
	      wp_event verify_monad
	        (composition_fri_verifier_tied_missing_sampled_layer_chain
	          (verifier_state_from_adversary attacker_state
	            (staged_proof_transcript data)))
	        (verifier_state_from_adversary attacker_state
	          (staged_proof_transcript data)) \<le>
	        (((Merkle + Missing) + Next + Successor + Final + Merkle) +
	          Slot + Zero)"
	  proof -
	    fix data attacker_state
	    assume support:
	      "Some (data, attacker_state) \<in>
	        set_dist (execute (checked_staged_transcript_program A)
	          adversary_initial_state)"
	    let ?s =
	      "verifier_state_from_adversary attacker_state
	        (staged_proof_transcript data)"
	    show "wp_event verify_monad
	        (composition_fri_verifier_tied_missing_sampled_layer_chain ?s) ?s
	        \<le>
	        (((Merkle + Missing) + Next + Successor + Final + Merkle) +
	          Slot + Zero)"
	      by (rule
	          wp_composition_fri_verifier_tied_missing_sampled_layer_chain_bound_from_residual_gaps)
	        (rule slot_bound[OF support],
	         rule merkle_bound[OF support],
	         rule missing_bound[OF support],
	         rule next_bound[OF support],
	         rule successor_bound[OF support],
	         rule final_bound[OF support],
	         rule zero_bound[OF support])
	  qed
	  show ?thesis
	    by (rule
	        checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_sampled_and_missing
	        [OF sampled missing])
	qed

end

end
