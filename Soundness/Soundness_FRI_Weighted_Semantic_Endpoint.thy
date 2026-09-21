(* Title: Stark/Soundness_FRI_Weighted_Semantic_Endpoint.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Semantic_Endpoint
  imports
    "Soundness_FRI_Weighted_Semantic_Portfolio"
begin

section \<open>Semantic Endpoint for weighted MCA soundness\<close>

text \<open>Replay the original decoded-semantic query-list event through every verifier repetition. The result is guarded and is assembled with its exception costs only in the complete soundness theory.\<close>

subsection \<open>Long Path Query Replay\<close>

context soundness
begin

lemma lpq_header_step:
  assumes header: "as_header U start data"
    and route: "ro_absorb_lookup_chain (channel_for_hash_map U) start xs v"
  shows "as_header U v data"
proof -
  obtain rest where shape: "weighted_semantic_header_shape data" and active: "staged_trace_fri_roots data\<noteq>[]"
    and chain: "ro_absorb_lookup_chain (channel_for_hash_map U) (PState adversary_initial_state)
      (weighted_semantic_header data@rest) start"
    using header unfolding as_header_def by blast
  have "ro_absorb_lookup_chain (channel_for_hash_map U) (PState adversary_initial_state)
      (weighted_semantic_header data@(rest@xs)) v"
    using ro_absorb_lookup_chain_append[OF chain route] by simp
  then show ?thesis unfolding as_header_def using shape active by blast
qed

lemma lpq_ntimes_path:
  fixes s t :: "'f protocol_channel"
  assumes power: "clength*scale=2^N"
    and lenf: "length ffs\<le>N" and lenc: "length cfs\<le>N"
    and clean: "\<not>hash_map_output_collision (channel_for_hash_map U)"
    and out: "Some(results,t)\<in>set_dist
      (execute (ntimes (ro_verifier_query_round_program rt ffs fv alphas cfs cv) n) s)"
    and ext: "t\<le>channel_for_hash_map U"
    and len: "length raws=n" "length chunks=n"
    and shapes: "\<forall>k<n. verifier_query_round_chunk (index(to_nat(raws!k))) (map snd ffs) (map snd cfs) (chunks!k)"
    and tr: "PTranscript s=List.concat chunks@rest"
    and header: "as_header U (PState s) data"
    and members: "\<forall>raw\<in>set raws. index(to_nat raw)\<in>weighted_semantic_indices rT rC U data"
    and lookups: "\<And>k v. k<n \<Longrightarrow>
      ro_absorb_lookup_chain (channel_for_hash_map U) (PState s) (List.concat(take k chunks)) v \<Longrightarrow>
      fmlookup U (QueryIndexChallenge (PQueryCounter s+k) v)=Some(raws!k)"
  shows "lps_semantic_path rT rC rt ffs cfs U n (PQueryCounter s) (PState s)"
  using out len shapes tr header members lookups
proof (induction n arbitrary: s raws chunks results rest)
  case 0 then show ?case by simp
next
  case (Suc n)
  obtain raw rs where raws: "raws=raw#rs" and rlen: "length rs=n"
    using Suc.prems(2) by (cases raws) auto
  obtain chunk cs where chunks: "chunks=chunk#cs" and clen: "length cs=n"
    using Suc.prems(3) by (cases chunks) auto
  obtain mid results' where first: "Some((),mid)\<in>set_dist
      (execute (ro_verifier_query_round_program rt ffs fv alphas cfs cv) s)"
    and tail: "Some(results',t)\<in>set_dist
      (execute (ntimes (ro_verifier_query_round_program rt ffs fv alphas cfs cv) n) mid)"
    using Suc.prems(1) by (auto elim!: set_dist_bindE)
  have mt: "mid\<le>t" by (rule vr_ntimes_extends[OF tail])
  have mU: "mid\<le>channel_for_hash_map U" by (rule hash_ext_trans[OF mt ext])
  have headshape: "verifier_query_round_chunk (index(to_nat raw)) (map snd ffs) (map snd cfs) chunk"
    using Suc.prems(4)[rule_format, of 0] by (simp add: raws chunks)
  have trhead: "PTranscript s=chunk@(List.concat cs@rest)" using Suc.prems(5) by (simp add: chunks)
  have aligned: "PTranscript mid=List.concat cs@rest \<and>
      ro_absorb_lookup_chain mid (PState s) chunk (PState mid) \<and> s\<le>mid \<and>
      PQueryCounter mid=Suc(PQueryCounter s)"
    by (rule ro_verifier_query_round_program_aligns_expected_chunk[OF headshape trhead refl refl first])
  have chain: "ro_absorb_lookup_chain (channel_for_hash_map U) (PState s) chunk (PState mid)"
    by (rule ro_absorb_lookup_chain_mono[OF _ mU]) (use aligned in simp)
  have lookup: "fmlookup U (QueryIndexChallenge (PQueryCounter s) (PState s))=Some raw"
    using Suc.prems(8)[of 0 "PState s"] by (simp add: raws)
  obtain actual_raw where stored: "fmlookup (HashMap mid)
      (QueryIndexChallenge (PQueryCounter s) (PState s))=Some actual_raw"
    and fiber: "actual_raw\<in>pair_route_fiber UNIV rt ffs cfs (PState s) mid (PState mid)"
    by (rule pair_route_from_success[OF power lenf lenc first]) blast
  have storedU: "fmlookup U (QueryIndexChallenge (PQueryCounter s) (PState s))=Some actual_raw"
    using hash_extension_lookup[OF stored mU] by (simp add: channel_for_hash_map_def)
  have raw_eq: "actual_raw=raw" using storedU lookup by simp
  have fiberU: "raw\<in>pair_route_fiber UNIV rt ffs cfs (PState s) (channel_for_hash_map U) (PState mid)"
    by (rule subsetD[OF causal_route_mono[OF mU]]) (use fiber in \<open>simp only: raw_eq\<close>)
  have edge: "lpa_route rt ffs cfs U (PQueryCounter s,PState s) raw=Some(PState mid)"
    by (rule lpa_route_someI[OF clean]) (simp add: fiberU)
  have ready: "weighted_semantic_ready rT rC U (PState s) (weighted_semantic_indices rT rC U data)"
    by (rule lps_header_ready[OF Suc.prems(6)])
  have member: "index(to_nat raw)\<in>weighted_semantic_indices rT rC U data"
    using Suc.prems(7) by (simp add: raws)
  have hit: "weighted_semantic_hit rT rC U (PState s) raw"
    unfolding weighted_semantic_hit_def
    apply (rule exI[of _ "weighted_semantic_indices rT rC U data"], intro conjI)
     apply (rule ready)
    using member by (simp add: query_index_raw_preimage_def)
  have shapes': "\<forall>k<n. verifier_query_round_chunk (index(to_nat(rs!k))) (map snd ffs) (map snd cfs) (cs!k)"
    using Suc.prems(4) by (auto simp: raws chunks dest: spec[where x="Suc _"])
  have header': "as_header U (PState mid) data" by (rule lpq_header_step[OF Suc.prems(6) chain])
  have members': "\<forall>raw\<in>set rs. index(to_nat raw)\<in>weighted_semantic_indices rT rC U data"
    using Suc.prems(7) by (simp add: raws)
  have lookup': "fmlookup U (QueryIndexChallenge (PQueryCounter mid+k) v)=Some(rs!k)"
    if k: "k<n" and path: "ro_absorb_lookup_chain (channel_for_hash_map U)
      (PState mid) (List.concat(take k cs)) v" for k v
  proof -
    have full: "ro_absorb_lookup_chain (channel_for_hash_map U) (PState s)
        (List.concat(take (Suc k) chunks)) v"
      using ro_absorb_lookup_chain_append[OF chain path] by (simp add: chunks)
    show ?thesis using Suc.prems(8)[OF _ full] k aligned by (simp add: raws)
  qed
  have tailpath: "lps_semantic_path rT rC rt ffs cfs U n (PQueryCounter mid) (PState mid)"
    by (rule Suc.IH[OF tail rlen clen shapes' _ header' members' lookup']) (use aligned in simp)
  show ?case using lookup hit edge tailpath aligned by (auto simp: lpa_samples_def)
qed

end

subsection \<open>Long Path Initial Replay\<close>

context soundness
begin

lemma lpr_initial_decoded_path:
 fixes final_state :: "'f protocol_channel"
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength"
   and builder_out: "Some (((prefix,prefix_state),data,query_start,raws,query_states),attacker_state)
     \<in>set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and verifier_out: "Some (results,final_state)\<in>set_dist (execute ro_verify_monad
     (verifier_state_from_adversary attacker_state (staged_proof_transcript data)))"
   and clean: "\<not>hash_map_output_collision final_state"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values final_state"
   and positive: "0<rounds"
    and power: "clength*scale=2^N"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log (maxDegree+1)\<le>N"
   and members: "\<forall>raw\<in>set raws. index(to_nat raw)\<in>weighted_semantic_indices rT rC (HashMap final_state) data"
 shows "lpu_event rT rC rounds 0 (Some (result,final_state))"
proof -
  from ro_checked_staged_transcript_program_with_first_root_outcomeE[
      OF builder_out]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
    and after_out:
      "Some (head_data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              prefix)
            prefix_final)"
    and query_out:
      "Some ((raws, query_states, query_chunks), attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots head_data)
              (staged_composition_fri_roots head_data)
              query_start 0 rounds)
            query_start)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    by blast

  obtain fr prefix_trace_bs first_root where
    prefix_eq: "prefix = (fr, prefix_trace_bs, first_root)"
    by (cases prefix) auto
  have prefix_props:
      "prefix_trace_bs = [] \<and>
       prefix_state = prefix_final \<and>
       adversary_initial_state \<le> prefix_final \<and>
       ro_absorb_lookup_chain prefix_final
         (PState adversary_initial_state) [fr, first_root]
         (PState prefix_final) \<and>
       PQueryCounter prefix_final = PQueryCounter adversary_initial_state"
    by (rule ro_staged_first_trace_fri_root_prefix_program_chain[
          OF wf controlled nonempty])
      (use prefix_out prefix_eq in simp)
  have after_fields:
      "staged_trace_root head_data = fr \<and>
       (\<exists>roots. staged_trace_fri_roots head_data = first_root # roots)"
    by (rule
        ro_checked_staged_after_first_trace_fri_root_prefix_program_fields[
          OF nonempty])
      (use after_out prefix_eq in simp)

  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
        ro_checked_staged_transcript_program_with_first_root_projection_outcome[
          OF nonempty builder_out])
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength \<and>
       length (staged_alphas data) = length spec \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       length (staged_composition_fri_challenges data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       ceil_log (to_nat (staged_degree data) + 1) \<le>
         ceil_log (maxDegree + 1) \<and>
       length (staged_query_chunks data) = rounds"
    by (rule ro_checked_staged_transcript_program_outcome_shape[
          OF original_out])
  have query_bound:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_props:
      "length raws = rounds \<and>
       length query_states = rounds \<and>
       length query_chunks = rounds \<and>
       query_start \<le> attacker_state \<and>
       PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
       (\<forall>j < rounds.
         query_states ! j \<le> attacker_state \<and>
         PQueryCounter (query_states ! j) =
           PQueryCounter query_start + j \<and>
         fmlookup (HashMap attacker_state)
           (QueryIndexChallenge
             (PQueryCounter (query_states ! j))
             (PState (query_states ! j))) =
           Some (raws ! j) \<and>
         verifier_query_round_chunk (index (to_nat (raws ! j)))
           (staged_trace_fri_roots head_data)
           (staged_composition_fri_roots head_data)
           (query_chunks ! j)) \<and>
       (\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale)"
    by (rule ro_checked_staged_query_program_with_witnesses_outcome[
          OF controlled query_bound query_out])

  have boundary_trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    using shape by simp
  have boundary_composition_len:
      "length (staged_composition_fri_roots data) =
        ceil_log (to_nat (staged_degree data) + 1)"
    using shape by simp
  have boundary_alphas_len:
      "length (staged_alphas data) = length spec"
    using shape by simp
  have boundary_query_idxs_len:
      "length (map (\<lambda>raw. index (to_nat raw)) raws) = rounds"
    using query_props by simp
  have boundary_chunks_len:
      "length (staged_query_chunks data) = rounds"
    using shape by simp
  have boundary_chunk_shapes:
      "\<forall>j < rounds.
        verifier_query_round_chunk
          (map (\<lambda>raw. index (to_nat raw)) raws ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)"
    using query_props data_eq by simp

  from ro_verify_monad_actual_query_boundaryE[
      OF nonempty boundary_trace_len boundary_composition_len
        boundary_alphas_len boundary_query_idxs_len boundary_chunks_len
        boundary_chunk_shapes verifier_out]
  obtain f_fl fl verifier_query_state verifier_fr f_final alphas final where
    verifier_fr_eq: "verifier_fr = staged_trace_root data"
    and trace_roots_eq:
      "map snd f_fl = staged_trace_fri_roots data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and f_fl_nonempty: "f_fl \<noteq> []"
    and verifier_query_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program verifier_fr f_fl f_final
                alphas fl final)
              rounds)
            verifier_query_state)"
    and verifier_transcript:
      "PTranscript verifier_query_state =
        List.concat (staged_query_chunks data)"
    and attacker_verifier_ext:
      "attacker_state \<le> verifier_query_state"
    and verifier_counter:

      "PQueryCounter verifier_query_state = 0"
    and verifier_chain:
      "ro_absorb_lookup_chain final_state (PState verifier_query_state)
        (List.concat (staged_query_chunks data)) (PState final_state)"
    and verifier_ext: "verifier_query_state \<le> final_state"
    .

  have attacker_final_ext: "attacker_state \<le> final_state"
    by (rule hash_ext_trans[OF attacker_verifier_ext verifier_ext])
  have builder_chain_attacker:
      "ro_absorb_lookup_chain attacker_state (PState query_start)
        (List.concat query_chunks) (PState attacker_state)"
    using ro_checked_staged_query_program_with_witnesses_absorb_lookup_chain[
      OF controlled query_bound query_out]
    by blast
  have builder_chain_final:
      "ro_absorb_lookup_chain final_state (PState query_start)
        (List.concat query_chunks) (PState attacker_state)"
    by (rule ro_absorb_lookup_chain_mono[
          OF builder_chain_attacker attacker_final_ext])

  have sync:
      "PState final_state = PState attacker_state \<and>
       PTranscript final_state = [] \<and>
       verifier_state_from_adversary attacker_state
         (staged_proof_transcript data) \<le> final_state \<and>
       PQueryCounter final_state = rounds"
    by (rule ro_checked_staged_transcript_program_ro_verify_monad_sync[
          OF wf controlled original_out verifier_out])
  have builder_chain_final':
      "ro_absorb_lookup_chain final_state (PState query_start)
        (List.concat (staged_query_chunks data)) (PState final_state)"
    using builder_chain_final sync data_eq by simp
  have verifier_builder_state:
      "PState verifier_query_state = PState query_start"
    by (rule ro_absorb_lookup_chain_start_functional_if_clean[
          OF clean verifier_chain builder_chain_final'])

  have good_fields:
      "prefix_state \<le> attacker_state \<and> PQueryCounter query_start = 0"
    by (rule
        ro_checked_staged_transcript_program_with_first_root_good_fields[
          OF wf controlled nonempty builder_out])

  have j0: "0<rounds" by (rule positive)
  have clean_sent: "\<not>hash_map_output_collision attacker_state"
    using hash_map_output_collision_mono[OF _ attacker_final_ext] clean by blast
  note chain0=ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain[
    OF wf controlled nonempty builder_out clean_sent j0]
  have header_sent: "ro_absorb_lookup_chain attacker_state (PState adversary_initial_state)
      (weighted_semantic_header data) (PState query_start)"
    using chain0 by (simp add: weighted_semantic_header_def)
  have header_final: "ro_absorb_lookup_chain final_state (PState adversary_initial_state)
      (weighted_semantic_header data) (PState query_start)"
    by (rule ro_absorb_lookup_chain_mono[OF header_sent attacker_final_ext])
  have header_map: "ro_absorb_lookup_chain (channel_for_hash_map (HashMap final_state))
      (PState adversary_initial_state) (weighted_semantic_header data) (PState verifier_query_state)"
  proof -
    have maps: "HashMap (channel_for_hash_map (HashMap final_state))=HashMap final_state"
      by (simp add: channel_for_hash_map_def)
    show ?thesis
      using header_final by (simp only: ro_absorb_lookup_chain_cong_hash_map[OF maps] verifier_builder_state)
  qed
  have header: "as_header (HashMap final_state) (PState verifier_query_state) data"
    unfolding as_header_def
    using shape nonempty header_map
    by (auto simp: weighted_semantic_header_shape_def intro!: exI[of _ "[]"])
  have lenff: "length f_fl\<le>N" using trace_roots_eq shape lenf by (metis length_map)
  have lenfl: "length fl\<le>N" using composition_roots_eq shape lenc by (metis length_map order_trans)
  have mapclean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap final_state))"
    using clean by (simp add: hash_map_output_collision_def channel_for_hash_map_def)
  have mapinitial: "PState adversary_initial_state\<notin>hash_map_output_values
      (channel_for_hash_map (HashMap final_state))"
    using initial by (simp add: hash_map_output_values_def channel_for_hash_map_def)
  have lookups: "fmlookup (HashMap final_state) (QueryIndexChallenge (PQueryCounter verifier_query_state+k) v)=
      Some(raws!k)"
    if k: "k<rounds" and chain: "ro_absorb_lookup_chain
      (channel_for_hash_map (HashMap final_state)) (PState verifier_query_state)
      (List.concat(take k (staged_query_chunks data))) v" for k v
  proof -
    note bk=ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain[
      OF wf controlled nonempty builder_out clean_sent k]
    have bchain: "ro_absorb_lookup_chain attacker_state (PState query_start)
      (List.concat(take k (staged_query_chunks data))) (PState(query_states!k))"
      using bk by blast
    have finalchain: "ro_absorb_lookup_chain final_state (PState query_start)
      (List.concat(take k (staged_query_chunks data))) (PState(query_states!k))"
      by (rule ro_absorb_lookup_chain_mono[OF bchain attacker_final_ext])
    have chain': "ro_absorb_lookup_chain final_state (PState query_start)
      (List.concat(take k (staged_query_chunks data))) v"
    proof -
      have maps: "HashMap(channel_for_hash_map (HashMap final_state))=HashMap final_state"
        by (simp add: channel_for_hash_map_def)
      show ?thesis using chain
        by (simp only: ro_absorb_lookup_chain_cong_hash_map[OF maps] verifier_builder_state)
    qed
    have eq: "v=PState(query_states!k)"
      by (rule ro_absorb_lookup_chain_functional[OF chain' finalchain])
    have stored: "fmlookup (HashMap attacker_state) (QueryIndexChallenge k (PState(query_states!k)))=Some(raws!k)"
      using query_props good_fields k
      apply simp
      by metis
    show ?thesis using hash_extension_lookup[OF stored attacker_final_ext]
      by (simp add: verifier_counter eq)
  qed
  have path: "lps_semantic_path rT rC verifier_fr f_fl fl (HashMap final_state)
      rounds (PQueryCounter verifier_query_state) (PState verifier_query_state)"
    by (rule lpq_ntimes_path[OF power lenff lenfl mapclean verifier_query_out,
      where raws=raws and chunks="staged_query_chunks data" and rest="[]" and data=data])
      (use query_props shape boundary_chunk_shapes verifier_transcript trace_roots_eq
        composition_roots_eq header members lookups in
        \<open>auto simp: less_eq_hash_ext_def less_eq_fmap_def channel_for_hash_map_def\<close>)
  show ?thesis unfolding lpu_event_def
    apply (simp only: option.simps prod.case)
    apply (intro conjI mapclean mapinitial)
    apply (rule exI[of _ "PState verifier_query_state"], rule exI[of _ data],
      rule exI[of _ verifier_fr], rule exI[of _ f_fl], rule exI[of _ fl])
    using header verifier_fr_eq trace_roots_eq composition_roots_eq path verifier_counter by simp
qed

end

subsection \<open>Long Path Residual Endpoint\<close>

context soundness
begin

lemma lpr_original_semantic_list_path:
 fixes final_state :: "'f protocol_channel"
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength"
   and builder_out: "Some (((prefix,prefix_state),data,query_start,raws,query_states),attacker_state)
     \<in>set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and verifier_out: "Some (results,final_state)\<in>set_dist (execute ro_verify_monad
     (verifier_state_from_adversary attacker_state (staged_proof_transcript data)))"
   and clean: "\<not>hash_map_output_collision final_state"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values final_state"
   and positive: "0<rounds"
   and power: "clength*scale=2^N"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log (maxDegree+1)\<le>N"

   and no_trace: "\<not>hash_map_new_output_hit
     (first_trace_fri_root_prefix_merkle_targets prefix prefix_state) prefix_state final_state"
   and no_comp: "\<not>hash_map_new_output_hit
     (ro_actual_query_composition_prefix_targets data query_start) query_start final_state"
   and list_hit: "map (\<lambda>raw. index (to_nat raw)) raws\<in>
     ro_mca_decoded_semantic_query_lists rT rC prefix prefix_state data query_start"
 shows "lpu_event rT rC rounds 0 (Some (result,final_state))"
proof -
 have original_out: "Some (data,attacker_state)\<in>set_dist
     (execute (ro_checked_staged_transcript_program A) adversary_initial_state)"
   by (rule ro_checked_staged_transcript_program_with_first_root_projection_outcome[OF nonempty builder_out])
 have transfer: "attacker_state\<le>verifier_state_from_adversary attacker_state (staged_proof_transcript data)"
   by (rule hash_extends_verifier_state_from_adversary_right) (rule hash_ext_refl)
 have replay: "verifier_state_from_adversary attacker_state (staged_proof_transcript data)\<le>final_state"
   using ro_checked_staged_transcript_program_ro_verify_monad_sync[OF wf controlled original_out verifier_out] by blast
 have af: "attacker_state\<le>final_state" by (rule hash_ext_trans[OF transfer replay])
 have ac: "\<not>hash_map_output_collision attacker_state"
   using hash_map_output_collision_mono[OF _ af] clean by blast
 have pa: "prefix_state\<le>attacker_state"
   using ro_checked_staged_transcript_program_with_first_root_good_fields[OF wf controlled nonempty builder_out] by blast
 have qa: "query_start\<le>attacker_state"
   using ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[OF wf controlled builder_out] by blast
 have j0: "0<rounds" using positive by simp
 have pref: "prefix=(staged_trace_root data,[],hd (staged_trace_fri_roots data))"
   using ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain[
     OF wf controlled nonempty builder_out ac j0] by blast
 note facts=af ac pa qa pref
 have su: "prefix_state\<le>final_state" by (rule hash_ext_trans[OF facts(3) facts(1)])
 have qu: "query_start\<le>final_state" by (rule hash_ext_trans[OF facts(4) facts(1)])
 have prefix_clean: "\<not>hash_map_output_collision prefix_state"
   using hash_map_output_collision_mono[OF _ su] clean by blast
 have transport: "ro_mca_decoded_semantic_query_indices rT rC prefix prefix_state data query_start=
     weighted_semantic_indices rT rC (HashMap final_state) data"
   by (rule weighted_semantic_transport[OF facts(5) su qu prefix_clean no_trace no_comp])
 have len: "length raws=rounds" and members:
   "\<forall>raw\<in>set raws. index (to_nat raw)\<in>ro_mca_decoded_semantic_query_indices rT rC prefix prefix_state data query_start"
   using list_hit unfolding ro_mca_decoded_semantic_query_lists_def fri_conditioned_query_lists_def by auto
  have final_members: "\<forall>raw\<in>set raws. index(to_nat raw)\<in>weighted_semantic_indices rT rC (HashMap final_state) data"
    using members transport by simp
  show ?thesis
    by (rule lpr_initial_decoded_path[OF wf controlled nonempty builder_out verifier_out clean initial
      positive power lenf lenc final_members])
qed

lemma lpr_path_map:
 fixes m :: "('a, 'f protocol_channel) state_monad"
 shows "wp_event (m \<bind> (\<lambda>x. return (f x))) (lpu_event rT rC n j) s=
   wp_event m (lpu_event rT rC n j) s"
proof -
 have pair: "lpu_event rT rC n j (Some (f x,t))=lpu_event rT rC n j (Some (x,t))" for x and t :: "'f protocol_channel"
   by (simp only: lpu_event_def option.simps prod.case)
 have none: "\<not>lpu_event rT rC n j None"
   by (simp add: lpu_event_def)
 show ?thesis unfolding wp_event_def wp_bind_return_map
   apply (rule arg_cong[where f="\<lambda>P. wp m P s"], rule ext)
   subgoal for out
     by (cases out) (auto simp only: option.simps prod.case pair none split: prod.splits)
   done
qed

lemma lpr_witness_path_probability:
 "wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
    (lpu_event rT rC n j) s=
  wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
    (lpu_event rT rC n j) s"
proof -
 have a: "wp_event (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
    (lpu_event rT rC n j) s=
  wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
    (lpu_event rT rC n j) s"
   using lpr_path_map[where m="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A"
     and f="\<lambda>(((prefix_with_state,data,query_start,raws,query_states),attacker_state),result).
       (((data,query_start,raws,query_states),attacker_state),result)"
     and rT=rT and rC=rC and n=n and j=j and s=s]
   by (simp only: split_def ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection_all_rounds[unfolded split_def])
 have b: "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
    (lpu_event rT rC n j) s=
  wp_event (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
    (lpu_event rT rC n j) s"
   using lpr_path_map[where m="ro_absorb_checked_staged_security_experiment_with_query_witnesses A"
     and f="\<lambda>(((data,query_start,raws,query_states),attacker_state),result).
       ((data,attacker_state),result)"
     and rT=rT and rC=rC and n=n and j=j and s=s]
   by (simp only: split_def ro_absorb_checked_staged_security_experiment_with_query_witnesses_projection[unfolded split_def])
 show ?thesis using a b by simp
qed

lemma lpr_clean_semantic_on_support:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength"
   and positive: "0<rounds"
   and power: "clength*scale=2^N"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log (maxDegree+1)\<le>N"
   and supported: "out\<in>set_dist (execute
     (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and event: "vr_clean_semantic_event rT rC out"
 shows "lpu_event rT rC rounds 0 out"
proof -
 obtain prefix prefix_state data query_start raws query_states attacker_state results u where
   out: "out=Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)"
   and clean: "\<not>hash_map_output_collision u"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values u"
   and no_trace: "\<not>hash_map_new_output_hit
      (first_trace_fri_root_prefix_merkle_targets prefix prefix_state) prefix_state u"
   and no_comp: "\<not>hash_map_new_output_hit
      (ro_actual_query_composition_prefix_targets data query_start) query_start u"
   and hit: "map (\<lambda>raw. index (to_nat raw)) raws\<in>
      ro_mca_decoded_semantic_query_lists rT rC prefix prefix_state data query_start"
   using event unfolding vr_clean_semantic_event_def by (auto split: option.splits prod.splits)
 have support': "Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)
   \<in>set_dist (execute
     (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
       adversary_initial_state)" using supported out by simp
 have pair: "lpu_event rT rC rounds 0
     (Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u))"
 proof (rule ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_outcomeE[OF support'])
  assume builder: "Some (((prefix,prefix_state),data,query_start,raws,query_states),attacker_state)
     \<in>set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and verifier: "Some (results,u)\<in>set_dist (execute ro_verify_monad
     (verifier_state_from_adversary attacker_state (staged_proof_transcript data)))"
  show ?thesis
    by (rule lpr_original_semantic_list_path[OF wf controlled nonempty builder verifier clean initial positive power
        lenf lenc no_trace no_comp hit])
 qed
 show ?thesis using pair out by simp
qed

lemma lpr_clean_semantic_bound:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength"
   and positive: "0<rounds"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log (maxDegree+1)\<le>N"
   and power: "clength*scale=2^N"
 shows "wp_event
    (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
    (vr_clean_semantic_event rT rC) adversary_initial_state \<le>
   nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*(ro_mca_weighted_semantic_base rT rC)^rounds+
   fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
proof -
 let ?run="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A"
 have "wp_event ?run (vr_clean_semantic_event rT rC) adversary_initial_state\<le>
     wp_event ?run (lpu_event rT rC rounds 0) adversary_initial_state"
   unfolding wp_event_def
   by (rule wp_mono_on_support)
     (use lpr_clean_semantic_on_support[OF wf controlled nonempty positive power lenf lenc] in auto)
 also have "...=wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
     (lpu_event rT rC rounds 0) adversary_initial_state" by (rule lpr_witness_path_probability)
 also have "...\<le>nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*(ro_mca_weighted_semantic_base rT rC)^rounds+
   fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
   by (rule lpu_saved_experiment_bound[OF wf controlled])
 finally show ?thesis .
qed


end

end
