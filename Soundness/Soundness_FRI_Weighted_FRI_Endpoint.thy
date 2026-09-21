(* Title: Stark/Soundness_FRI_Weighted_FRI_Endpoint.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_FRI_Endpoint
  imports
    "Soundness_FRI_Weighted_Challenge_Portfolio"
begin

section \<open>FRI Endpoint for weighted MCA soundness\<close>

text \<open>Replay the actual trace/composition whole-list residual events against the shared final map. No per-position union or independence between the two FRI branches is assumed.\<close>

subsection \<open>Challenge Query Replay\<close>

context soundness
begin

lemma cqr_ntimes_path:
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
    and members: "\<forall>raw\<in>set raws. raw\<in>S"
    and lookups: "\<And>k v. k<n \<Longrightarrow>
      ro_absorb_lookup_chain (channel_for_hash_map U) (PState s) (List.concat(take k chunks)) v \<Longrightarrow>
      fmlookup U (QueryIndexChallenge (PQueryCounter s+k) v)=Some(raws!k)"
  shows "lpw_accept S (lpa_route rt ffs cfs U) (lpa_samples U) n (PQueryCounter s) (PState s)"
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
  have hit: "raw\<in>S" using Suc.prems(7) by (simp add: raws)
  have shapes': "\<forall>k<n. verifier_query_round_chunk (index(to_nat(rs!k))) (map snd ffs) (map snd cfs) (cs!k)"
    using Suc.prems(4) by (auto simp: raws chunks dest: spec[where x="Suc _"])
  have header': "as_header U (PState mid) data" by (rule lpq_header_step[OF Suc.prems(6) chain])
  have members': "\<forall>raw\<in>set rs. raw\<in>S"
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
  have tailpath: "lpw_accept S (lpa_route rt ffs cfs U) (lpa_samples U) n (PQueryCounter mid) (PState mid)"
    by (rule Suc.IH[OF tail rlen clen shapes' _ header' members' lookup']) (use aligned in simp)
  have sample: "lpa_samples U (PQueryCounter s,PState s)=Some raw"
    by (simp only: lpa_samples_def prod.sel lookup)
  have counter: "PQueryCounter mid=Suc(PQueryCounter s)" using aligned by simp
  show ?case unfolding lpw_accept.simps
    apply (rule exI[of _ raw], intro conjI sample hit)
    apply (rule disjI2, rule exI[of _ "PState mid"], intro conjI edge)
    using tailpath by (simp only: counter)
qed


end

subsection \<open>Challenge Initial Replay\<close>

context soundness
begin

lemma cir_initial_path:
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
   and members: "\<forall>raw\<in>set raws. raw\<in>S"
 shows "\<exists>start. as_header (HashMap final_state) start data \<and>
   lpw_accept S
     (lpa_route (staged_trace_root data)
       (map (\<lambda>root.((0::'f),root)) (staged_trace_fri_roots data))
       (map (\<lambda>root.((0::'f),root)) (staged_composition_fri_roots data)) (HashMap final_state))
     (lpa_samples (HashMap final_state)) rounds 0 start"
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
  have path: "lpw_accept S (lpa_route verifier_fr f_fl fl (HashMap final_state)) (lpa_samples (HashMap final_state))
      rounds (PQueryCounter verifier_query_state) (PState verifier_query_state)"
    by (rule cqr_ntimes_path[OF power lenff lenfl mapclean verifier_query_out,
      where raws=raws and chunks="staged_query_chunks data" and rest="[]" and data=data])
      (use query_props shape boundary_chunk_shapes verifier_transcript trace_roots_eq
        composition_roots_eq header members lookups in
        \<open>auto simp: less_eq_hash_ext_def less_eq_fmap_def channel_for_hash_map_def\<close>)
  have roots: "map snd f_fl=map snd (map (\<lambda>root.((0::'f),root)) (staged_trace_fri_roots data))"
      "map snd fl=map snd (map (\<lambda>root.((0::'f),root)) (staged_composition_fri_roots data))"
    using trace_roots_eq composition_roots_eq by (simp_all add: comp_def)
  have route: "lpa_route verifier_fr f_fl fl (HashMap final_state)=
    lpa_route (staged_trace_root data)
      (map (\<lambda>root.((0::'f),root)) (staged_trace_fri_roots data))
      (map (\<lambda>root.((0::'f),root)) (staged_composition_fri_roots data)) (HashMap final_state)"
    unfolding verifier_fr_eq by (rule lps_routes_roots_cong[OF roots])
  show ?thesis
    apply (rule exI[of _ "PState verifier_query_state"], intro conjI header)
    using path by (simp only: route verifier_counter)
qed

end

subsection \<open>Challenge Execution Evidence\<close>

context soundness
begin

lemma cee_builder_evidence:
 fixes u :: "'f protocol_channel"
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and outcome: "Some(data,t)\<in>set_dist(execute(ro_checked_staged_transcript_program A) adversary_initial_state)"
   and ext: "t\<le>u"
 shows "cvr_evidence (HashMap u) data"
proof -
 note facts=ro_checked_staged_transcript_program_conditioned_challenge_prefixes[OF wf controlled outcome]
 have chain: "ro_absorb_lookup_chain (channel_for_hash_map (HashMap u))
     (PState adversary_initial_state) xs v"
   if old: "ro_absorb_lookup_chain t (PState adversary_initial_state) xs v" for xs v
 proof -
   have new: "ro_absorb_lookup_chain u (PState adversary_initial_state) xs v"
     by (rule ro_absorb_lookup_chain_mono[OF old ext])
   have maps: "HashMap(channel_for_hash_map (HashMap u))=HashMap u"
     by (simp add: channel_for_hash_map_def)
   show ?thesis using new by (simp only: ro_absorb_lookup_chain_cong_hash_map[OF maps])
 qed
 have lookup: "fmlookup (HashMap u) k=Some z" if old: "fmlookup (HashMap t) k=Some z" for k z
   by (rule hash_extension_lookup[OF old ext])
 show ?thesis unfolding cvr_evidence_def ro_conditioned_trace_challenge_evidence_def
     ro_conditioned_composition_challenge_evidence_def
   using facts chain lookup by metis
qed

lemma cee_builder_final_extension:
 fixes u :: "'f protocol_channel"
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength"
   and builder: "Some (((prefix,prefix_state),data,query_start,raws,query_states),attacker_state)
     \<in>set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and verifier: "Some (results,u)\<in>set_dist (execute ro_verify_monad
     (verifier_state_from_adversary attacker_state (staged_proof_transcript data)))"
 shows "attacker_state\<le>u" "cvr_evidence (HashMap u) data"
proof -
 have original: "Some(data,attacker_state)\<in>set_dist
     (execute(ro_checked_staged_transcript_program A) adversary_initial_state)"
   by (rule ro_checked_staged_transcript_program_with_first_root_projection_outcome[OF nonempty builder])
 have transfer: "attacker_state\<le>verifier_state_from_adversary attacker_state (staged_proof_transcript data)"
   by (rule hash_extends_verifier_state_from_adversary_right) (rule hash_ext_refl)
 have replay: "verifier_state_from_adversary attacker_state (staged_proof_transcript data)\<le>u"
   using ro_checked_staged_transcript_program_ro_verify_monad_sync[OF wf controlled original verifier] by blast
 show ext: "attacker_state\<le>u" by (rule hash_ext_trans[OF transfer replay])
 show "cvr_evidence (HashMap u) data" by (rule cee_builder_evidence[OF wf controlled original ext])
qed

end

subsection \<open>Challenge Residual Endpoint\<close>

context soundness
begin

lemma cre_lists_map:
 "fri_mca_residual_query_lists N r b prefix prefix_state data
     (channel_for_hash_map (HashMap u)) =
  fri_mca_residual_query_lists N r b prefix prefix_state data u"
proof (rule fri_mca_residual_query_lists_stable)
 show "u\<le>channel_for_hash_map (HashMap u)"
   by (simp add: less_eq_hash_ext_def less_eq_fmap_def channel_for_hash_map_def)
 show "\<not>hash_map_new_output_hit (fri_checked_builder_merkle_targets data u)
     u (channel_for_hash_map (HashMap u))"
   by (auto simp: hash_map_new_output_hit_def channel_for_hash_map_def)
qed

lemma cre_branch_path:
 fixes u :: "'f protocol_channel"
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength"
   and builder: "Some (((prefix,prefix_state),data,query_start,raws,query_states),attacker_state)
     \<in>set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and verifier: "Some (results,u)\<in>set_dist (execute ro_verify_monad
     (verifier_state_from_adversary attacker_state (staged_proof_transcript data)))"
   and clean: "\<not>hash_map_output_collision u"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values u"
   and positive: "0<rounds" and power: "clength*scale=2^N"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log(maxDegree+1)\<le>N"
   and no_query: "\<not>hash_map_new_output_hit (fri_checked_builder_merkle_targets data query_start)
      query_start attacker_state"
   and no_builder: "\<not>fri_checked_builder_merkle_target_hit data attacker_state u"
   and hit: "map (\<lambda>raw. index(to_nat raw)) raws\<in>
     fri_mca_residual_query_lists N r b prefix prefix_state data query_start"
 shows "\<exists>start. as_header (HashMap u) start data \<and> cff_accept N r b rounds 0 data (HashMap u) start"
proof -
 have qa: "query_start\<le>attacker_state"
   using ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
     OF wf controlled builder] by blast
 have af: "attacker_state\<le>u"
   by (rule cee_builder_final_extension(1)[OF wf controlled nonempty builder verifier])
 have first: "fri_mca_residual_query_lists N r b prefix prefix_state data attacker_state=
     fri_mca_residual_query_lists N r b prefix prefix_state data query_start"
   by (rule fri_mca_residual_query_lists_stable[OF qa no_query])
 have second: "fri_mca_residual_query_lists N r b prefix prefix_state data u=
     fri_mca_residual_query_lists N r b prefix prefix_state data attacker_state"
   by (rule fri_mca_residual_query_lists_stable[OF af]) (use no_builder in \<open>simp add: fri_checked_builder_merkle_target_hit_def\<close>)
 have final_hit: "map (\<lambda>raw. index(to_nat raw)) raws\<in>
     fri_mca_residual_query_lists N r b prefix prefix_state data (channel_for_hash_map (HashMap u))"
   using hit by (simp only: cre_lists_map second first)
 have members: "\<forall>raw\<in>set raws. raw\<in>cff_raw N r b data (HashMap u)"
   using final_hit unfolding cff_raw_def fri_mca_residual_query_lists_def
     fri_conditioned_query_lists_def query_index_raw_preimage_def fri_mca_residual_query_indices_def
   by auto
 show ?thesis unfolding cff_accept_def
   by (rule cir_initial_path[OF wf controlled nonempty builder verifier clean initial positive power lenf lenc members])
qed

definition cre_event where
 "cre_event N rT rC out \<longleftrightarrow>
  (case out of None \<Rightarrow> False |
    Some(((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u) \<Rightarrow>
      \<not>hash_map_output_collision u \<and>
      PState adversary_initial_state\<notin>hash_map_output_values u \<and>
      \<not>hash_map_new_output_hit (fri_checked_builder_merkle_targets data query_start) query_start attacker_state \<and>
      \<not>fri_checked_builder_merkle_target_hit data attacker_state u \<and>
      map (\<lambda>raw. index(to_nat raw)) raws\<in>
        fri_mca_combined_query_lists N rT rC prefix prefix_state data query_start)"

lemma cre_original_guarded_iff:
 "cre_event N rT rC (Some(((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)) =
   (\<not>hash_map_output_collision u \<and>
    PState adversary_initial_state\<notin>hash_map_output_values u \<and>
    \<not>hash_map_new_output_hit (fri_checked_builder_merkle_targets data query_start) query_start attacker_state \<and>
    \<not>fri_checked_builder_merkle_target_hit data attacker_state u \<and>
    ro_query_head_dependent_actual_query_index_list_hit (fri_mca_combined_query_lists N rT rC)
      (Some (((prefix,prefix_state),data,query_start,raws,query_states),attacker_state)))"
 unfolding cre_event_def ro_query_head_dependent_actual_query_index_list_hit_def
   fri_mca_combined_query_lists_def
 by (simp add: fri_mca_residual_query_lists_head)

end

subsection \<open>Challenge Original Bound\<close>

context soundness
begin

lemma cob_on_support:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength" and positive: "0<rounds"
   and power: "clength*scale=2^N"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log(maxDegree+1)\<le>N"
   and supported: "out\<in>set_dist (execute
     (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and event: "cre_event N rT rC out"
 shows "cau_event N rT rC rounds 0 out"
proof -
 obtain prefix prefix_state data query_start raws query_states attacker_state results u where
   out: "out=Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)"
   and clean: "\<not>hash_map_output_collision u"
   and initial: "PState adversary_initial_state\<notin>hash_map_output_values u"
   and no_query: "\<not>hash_map_new_output_hit (fri_checked_builder_merkle_targets data query_start)
     query_start attacker_state"
   and no_builder: "\<not>fri_checked_builder_merkle_target_hit data attacker_state u"
   and hit: "map (\<lambda>raw. index(to_nat raw)) raws\<in>
     fri_mca_combined_query_lists N rT rC prefix prefix_state data query_start"
   using event unfolding cre_event_def by (auto split: option.splits prod.splits)
 have support': "Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)
     \<in>set_dist (execute (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
       adversary_initial_state)" using supported out by simp
 have claim: "cau_event N rT rC rounds 0
     (Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u))"
 proof (rule ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_outcomeE[OF support'])
   assume builder: "Some (((prefix,prefix_state),data,query_start,raws,query_states),attacker_state)
     \<in>set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
     and verifier: "Some(results,u)\<in>set_dist (execute ro_verify_monad
       (verifier_state_from_adversary attacker_state (staged_proof_transcript data)))"
   have ev: "cvr_evidence (HashMap u) data"
     by (rule cee_builder_final_extension(2)[OF wf controlled nonempty builder verifier])
   have either: "(\<exists>start. as_header (HashMap u) start data \<and> cff_accept N rT True rounds 0 data (HashMap u) start) \<or>
     (\<exists>start. as_header (HashMap u) start data \<and> cff_accept N rC False rounds 0 data (HashMap u) start)"
     using hit cre_branch_path[OF wf controlled nonempty builder verifier clean initial
       positive power lenf lenc no_query no_builder]
     unfolding fri_mca_combined_query_lists_def by blast
   show ?thesis using either ev clean initial
     unfolding cau_event_def
     by (auto simp: hash_map_output_collision_def hash_map_output_values_def channel_for_hash_map_def)
 qed
 show ?thesis using claim out by simp
qed

lemma cob_path_map:
 fixes m :: "('a, 'f protocol_channel) state_monad"
 shows "wp_event (m \<bind> (\<lambda>x. return (f x))) (cau_event N rT rC n j) s=
   wp_event m (cau_event N rT rC n j) s"
proof -
 have pair: "cau_event N rT rC n j (Some (f x,t))=cau_event N rT rC n j (Some (x,t))" for x and t :: "'f protocol_channel"
   by (simp only: cau_event_def option.simps prod.case)
 have none: "\<not>cau_event N rT rC n j None"
   by (simp add: cau_event_def)
 show ?thesis unfolding wp_event_def wp_bind_return_map
   apply (rule arg_cong[where f="\<lambda>P. wp m P s"], rule ext)
   subgoal for out
     by (cases out) (auto simp only: option.simps prod.case pair none split: prod.splits)
   done
qed

lemma cob_witness_path_probability:
 "wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
    (cau_event N rT rC n j) s=
  wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
    (cau_event N rT rC n j) s"
proof -
 have a: "wp_event (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
    (cau_event N rT rC n j) s=
  wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
    (cau_event N rT rC n j) s"
   using cob_path_map[where m="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A"
     and f="\<lambda>(((prefix_with_state,data,query_start,raws,query_states),attacker_state),result).
       (((data,query_start,raws,query_states),attacker_state),result)"
     and N=N and rT=rT and rC=rC and n=n and j=j and s=s]
   by (simp only: split_def ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection_all_rounds[unfolded split_def])
 have b: "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
    (cau_event N rT rC n j) s=
  wp_event (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
    (cau_event N rT rC n j) s"
   using cob_path_map[where m="ro_absorb_checked_staged_security_experiment_with_query_witnesses A"
     and f="\<lambda>(((data,query_start,raws,query_states),attacker_state),result).
       ((data,attacker_state),result)"
     and N=N and rT=rT and rC=rC and n=n and j=j and s=s]
   by (simp only: split_def ro_absorb_checked_staged_security_experiment_with_query_witnesses_projection[unfolded split_def])
 show ?thesis using a b by simp
qed

lemma cob_clean_fri_bound:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength" and positive: "0<rounds"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log(maxDegree+1)\<le>N"
   and power: "clength*scale=2^N"
 shows "wp_event
   (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
   (cre_event N rT rC) adversary_initial_state \<le>
     nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*
       ((ro_mca_weighted_fri_base rT True)^rounds+(ro_mca_weighted_fri_base rC False)^rounds)+
     fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
proof -
 let ?run="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A"
 have "wp_event ?run (cre_event N rT rC) adversary_initial_state\<le>
     wp_event ?run (cau_event N rT rC rounds 0) adversary_initial_state"
   unfolding wp_event_def
   by (rule wp_mono_on_support)
      (use cob_on_support[OF wf controlled nonempty positive power lenf lenc] in auto)
 also have "...=wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
     (cau_event N rT rC rounds 0) adversary_initial_state"
   by (rule cob_witness_path_probability)
 also have "... \<le>nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*
       ((ro_mca_weighted_fri_base rT True)^rounds+(ro_mca_weighted_fri_base rC False)^rounds)+
     fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
   using cau_saved_experiment_bound[OF wf controlled, where N=N and rT=rT and rC=rC
      and n=rounds and j=0] by (simp only: cap_cost_def)
 finally show ?thesis .
qed

end

end
