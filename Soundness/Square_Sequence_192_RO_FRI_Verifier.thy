(*  Title:      Stark/Square_Sequence_192_RO_FRI_Verifier.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Square_Sequence_192_RO_FRI_Verifier
 imports "Stark.Square_Sequence_192_RO_FRI_Algebra"
   "Stark.RO_Honest_Verifier_FRI_Chains"
begin

section \<open>Complete Honest Trace and Composition FRI Checks\<close>

text \<open>The actual RO FRI fold program carries each canonical committed polynomial value through all layers and passes its terminal assertion. Trace depth is ten; composition uses its original decoded-degree depth, including zero. The explicit tree, path, recording and replay-state conditions are local: this is not endpoint-only acceptance of the full RO verifier or an honest budget-fit claim.\<close>
context
  fixes a z :: field_192
    and combine :: "field_192 \<Rightarrow> field_192 \<Rightarrow> field_192"
begin
interpretation s: soundness combine field_generator_192 field_generator_192 64 1024 2
  stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
  "square_workload_spec 1024 a z" 640 "square_workload_spec2 1024 a z" 0 0 0
  by (rule square_192_soundness) simp


interpretation p: prover combine field_generator_192 field_generator_192 64 1024 2
  stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
  "square_workload_spec 1024 a z" 640 "square_trace_values 1024 a"
  by unfold_locales simp

lemma square_ro_polynomial_fri_chain_wp:
  fixes q :: "field_192 poly" and sent start :: "field_192 protocol_channel"
  assumes depth: "length bs\<le>16"
    and words: "map fst pairs =
      map (\<lambda>j. map (poly (square_ro_fold_poly q (take j bs)))
        (square_ro_fold_domain s.eval_domain (take j bs))) [0..<length bs]"
    and built: "\<And>xs tree. (xs,tree)\<in>set pairs \<Longrightarrow> protocol_created_tree xs tree sent"
    and paths: "\<And>xs tree k. (xs,tree)\<in>set pairs \<Longrightarrow>
      length (get_authentication_path (length xs) k tree)=floor_log (length xs)"
    and index: "idx<65536"
    and whole: "ro_absorb_lookup_chain sent (PState start) (List.concat (s.honest_fri_chunks pairs idx)) final"
    and ext: "sent\<le>start"
    and tr: "PTranscript start=List.concat (s.honest_fri_chunks pairs idx)@rest"
  shows "wp (mfold (idx,map (poly q) s.eval_domain!idx,65536,1)
      (s.ro_receive_query_commits (zip bs (map (value \<circ> snd) pairs)))) Q start =
    Q (Some ((idx mod (2^(16-length bs)),
      map (poly (square_ro_fold_poly q bs)) (square_ro_fold_domain s.eval_domain bs)!
        (idx mod (2^(16-length bs))),
      2^(16-length bs),2^length bs),
      start\<lparr>PState:=final,PTranscript:=rest\<rparr>))"
proof -
  let ?n = "length bs"
  let ?L = "\<lambda>j. map (poly (square_ro_fold_poly q (take j bs)))
    (square_ro_fold_domain s.eval_domain (take j bs))"
  let ?ix = "\<lambda>j. idx mod (2^(16-j))"
  let ?vs = "\<lambda>j. (?ix j,?L j!?ix j,2^(16-j),(2::nat)^j)"
  have plen: "length pairs=?n" using arg_cong[OF words, of length] by simp
  have word: "fst (pairs!j)=?L j" if "j<?n" for j
    using arg_cong[OF words, of "\<lambda>xs. xs!j"] that plen by simp
  have lens: "length (?L j)=(2::nat)^(16-j)" if j: "j\<le>?n" for j
  proof -
    have "length (take j bs)\<le>16" using depth j by simp
    from square_ro_fold_domain_power_length[OF this]
    show ?thesis using j by simp
  qed
  have pow: "length (fst (pairs!j))=2^(16-j)" if "j<?n" for j
    using lens[of j] word[OF that] that by simp
  have indices: "?ix j<length (fst (pairs!j))" if "j<?n" for j
    using pow[OF that] by simp
  have ct: "protocol_created_tree (fst (pairs!j)) (snd (pairs!j)) sent" if "j<?n" for j
    by (rule built) (use that plen in simp)
  have ap: "length (get_authentication_path (length (fst (pairs!j))) k (snd (pairs!j))) =
    floor_log (length (fst (pairs!j)))" if "j<?n" for j k
    by (rule paths) (use that plen in simp)
  have curr: "?vs j=(?ix j,fst (pairs!j)!?ix j,length (fst (pairs!j)),2^j)" if "j<?n" for j
    unfolding word[OF that]
    using lens[OF less_imp_le[OF that]] by simp
  have divides: "length (fst (pairs!k)) dvd length (fst (pairs!j))"
    if jk: "j<k" "k<length pairs" for j k
  proof -
    have "16-k\<le>16-j" using jk by arith
    then show ?thesis using jk plen pow[of j] pow[of k]
      by (simp add: le_imp_power_dvd)
  qed
  have chunks: "s.honest_fri_chunks pairs idx =
    map (\<lambda>j. s.honest_fri_pair_chunk (fst (pairs!j)) (snd (pairs!j)) (?ix j)) [0..<?n]"
    apply (subst s.honest_fri_chunks_flat)
    apply (rule divides; assumption)
    apply (rule nth_equalityI)
    using plen pow by (auto simp: case_prod_unfold s.honest_fri_pair_chunk_def Let_def)
  have succ: "?vs (Suc j) =
    (?ix j mod (length (fst (pairs!j)) div 2),
      (fst (pairs!j)!?ix j + fst (pairs!j)!((?ix j+length (fst (pairs!j)) div 2) mod length (fst (pairs!j)))) div 2 +
        bs!j * ((fst (pairs!j)!?ix j - fst (pairs!j)!((?ix j+length (fst (pairs!j)) div 2) mod length (fst (pairs!j)))) div
          (2*((s.h^?ix j)*field_generator_192)^(2^j))),
      length (fst (pairs!j)) div 2,2^j+2^j)" if j: "j<?n" for j
  proof -
    have j16: "j<16" using j depth by arith
    have diff: "16-j=Suc (16-Suc j)" using j16 by arith
    have half: "length (fst (pairs!j)) div 2=(2::nat)^(16-Suc j)"
      by (simp only: pow[OF j] diff power_Suc)
    have mod: "?ix j mod (length (fst (pairs!j)) div 2)=?ix (Suc j)"
      unfolding half by (rule mod_mod_cancel) (rule le_imp_power_dvd, simp)
    have take: "take j bs@[bs!j]=take (Suc j) bs"
      by (rule take_Suc_conv_app_nth[symmetric]) (rule j)
    have d: "length (take j bs)<16" using j j16 by simp
    have i: "?ix j<length (square_ro_fold_domain s.eval_domain (take j bs))"
      using indices[OF j] word[OF j] by simp
    note fold = square_ro_fold_expression_next_value[OF d i, where q=q and b="bs!j"]
    have short: "length (take j bs)=j" using j by simp
    note folded = fold[folded word[OF j], unfolded take short mod]
    have pwstep: "(2::nat)^Suc j=2^j+2^j" by simp
    show ?thesis
      apply (simp only: mod)
      apply (simp only: half prod.inject pwstep)
      apply (intro conjI)
      apply (rule refl)
      apply (rule sym)
      apply (rule folded[unfolded half])
      apply (rule refl)
      by (rule refl)
  qed
  have result: "wp (mfold (?vs 0) (s.ro_receive_query_commits (zip bs (map (value \<circ> snd) pairs)))) Q start =
    Q (Some (?vs ?n,start\<lparr>PState:=final,PTranscript:=rest\<rparr>))"
    by (rule s.ro_fri_chain_indexed_wp[OF plen refl ct pow indices ap curr succ chunks whole ext tr])
  show ?thesis using result index
    by (simp add: square_ro_fold_poly_def square_ro_fold_domain_def)
qed
lemma square_ro_polynomial_fri_terminal_wp:
  fixes q :: "field_192 poly" and sent start :: "field_192 protocol_channel"
  assumes depth: "length bs\<le>16"
    and words: "map fst pairs =
      map (\<lambda>j. map (poly (square_ro_fold_poly q (take j bs)))
        (square_ro_fold_domain s.eval_domain (take j bs))) [0..<length bs]"
    and built: "\<And>xs tree. (xs,tree)\<in>set pairs \<Longrightarrow> protocol_created_tree xs tree sent"
    and paths: "\<And>xs tree k. (xs,tree)\<in>set pairs \<Longrightarrow>
      length (get_authentication_path (length xs) k tree)=floor_log (length xs)"
    and index: "idx<65536"
    and whole: "ro_absorb_lookup_chain sent (PState start) (List.concat (s.honest_fri_chunks pairs idx)) final"
    and ext: "sent\<le>start"
    and tr: "PTranscript start=List.concat (s.honest_fri_chunks pairs idx)@rest"
    and deg: "degree (square_ro_fold_poly q bs)=0"
  shows "wp (mfold (idx,map (poly q) s.eval_domain!idx,65536,1)
      (s.ro_receive_query_commits (zip bs (map (value \<circ> snd) pairs))) \<bind>
        (\<lambda>(i,x,len,pw). assert (x=hd (map (poly (square_ro_fold_poly q bs))
          (square_ro_fold_domain s.eval_domain bs))))) Q start =
    Q (Some ((),start\<lparr>PState:=final,PTranscript:=rest\<rparr>))"
proof -
  have idx: "idx mod (2^(16-length bs)) < length (square_ro_fold_domain s.eval_domain bs)"
    by (simp add: square_ro_fold_domain_power_length[OF depth])
  note const_value = square_ro_fold_terminal_constant[OF depth deg idx]
  show ?thesis
    apply (subst wp_bind)
    apply (subst square_ro_polynomial_fri_chain_wp[OF depth words built paths index whole ext tr])
    by (auto simp: const_value assert_def wp_return)
qed

lemma square_ro_trace_fri_terminal_wp:
  fixes sent start :: "field_192 protocol_channel"
  assumes depth: "length bs=10"
    and words: "map fst pairs=map (\<lambda>j. square_ro_trace_layer a (take j bs)) [0..<10]"
    and built: "\<And>xs tree. (xs,tree)\<in>set pairs \<Longrightarrow> protocol_created_tree xs tree sent"
    and paths: "\<And>xs tree k. (xs,tree)\<in>set pairs \<Longrightarrow>
      length (get_authentication_path (length xs) k tree)=floor_log (length xs)"
    and index: "idx<65536"
    and whole: "ro_absorb_lookup_chain sent (PState start) (List.concat (s.honest_fri_chunks pairs idx)) final"
    and ext: "sent\<le>start"
    and tr: "PTranscript start=List.concat (s.honest_fri_chunks pairs idx)@rest"
  shows "wp (mfold (idx,square_ro_trace_layer a []!idx,65536,1)
      (s.ro_receive_query_commits (zip bs (map (value \<circ> snd) pairs))) \<bind>
        (\<lambda>(i,x,len,pw). assert (x=hd (square_ro_trace_layer a bs)))) Q start =
    Q (Some ((),start\<lparr>PState:=final,PTranscript:=rest\<rparr>))"
proof -
  have d: "length bs\<le>16" using depth by simp
  have w: "map fst pairs=map (\<lambda>j. map (poly (square_ro_fold_poly p.f (take j bs)))
    (square_ro_fold_domain s.eval_domain (take j bs))) [0..<length bs]"
    using words depth by (simp add: square_ro_trace_layer_def)
  have deg: "degree (square_ro_fold_poly p.f bs)=0"
    by (rule square_ro_trace_terminal_degree[OF depth])
  show ?thesis
    using square_ro_polynomial_fri_terminal_wp[OF d w built paths index whole ext tr deg, of Q]
    by (simp add: square_ro_trace_layer_def square_ro_fold_poly_def square_ro_fold_domain_def)
qed

lemma square_ro_composition_fri_terminal_wp:
  fixes sent start :: "field_192 protocol_channel"
  assumes endpoint: "z=a^(2^1023)"
    and depth: "length bs=ceil_log (stark_mod_ring_decode
      (stark_mod_ring_encode (degree (s.cp as p.f_powers)) :: field_192)+1)"
    and words: "map fst pairs=map (\<lambda>j. square_ro_composition_layer a z as (take j bs)) [0..<length bs]"
    and built: "\<And>xs tree. (xs,tree)\<in>set pairs \<Longrightarrow> protocol_created_tree xs tree sent"
    and paths: "\<And>xs tree k. (xs,tree)\<in>set pairs \<Longrightarrow>
      length (get_authentication_path (length xs) k tree)=floor_log (length xs)"
    and index: "idx<65536"
    and whole: "ro_absorb_lookup_chain sent (PState start) (List.concat (s.honest_fri_chunks pairs idx)) final"
    and ext: "sent\<le>start"
    and tr: "PTranscript start=List.concat (s.honest_fri_chunks pairs idx)@rest"
  shows "wp (mfold (idx,square_ro_composition_layer a z as []!idx,65536,1)
      (s.ro_receive_query_commits (zip bs (map (value \<circ> snd) pairs))) \<bind>
        (\<lambda>(i,x,len,pw). assert (x=hd (square_ro_composition_layer a z as bs)))) Q start =
    Q (Some ((),start\<lparr>PState:=final,PTranscript:=rest\<rparr>))"
proof -
  have d: "length bs\<le>16"
    using square_ro_composition_depth_bound[OF endpoint, of as] depth by arith
  have w: "map fst pairs=map (\<lambda>j. map (poly (square_ro_fold_poly (s.cp as p.f_powers) (take j bs)))
    (square_ro_fold_domain s.eval_domain (take j bs))) [0..<length bs]"
    using words by (simp add: square_ro_composition_layer_def)
  have deg: "degree (square_ro_fold_poly (s.cp as p.f_powers) bs)=0"
    by (rule square_ro_composition_terminal_degree[OF endpoint depth])
  show ?thesis
    using square_ro_polynomial_fri_terminal_wp[OF d w built paths index whole ext tr deg, of Q]
    by (simp add: square_ro_composition_layer_def square_ro_fold_poly_def square_ro_fold_domain_def)
qed

end

ML \<open>
  val _ = List.app (fn (name, expected, th) =>
    let val oracles = Thm_Deps.all_oracles [th]
    in
      if Thm.nprems_of th = expected andalso null (Thm.hyps_of th) andalso null oracles
      then writeln (name ^ ": checked " ^ string_of_int expected ^ " explicit premises")
      else error ("Unexpected FRI-chain dependency: " ^ name)
    end)
    [("square_ro_polynomial_fri_chain_wp", 8, @{thm square_ro_polynomial_fri_chain_wp}),
     ("square_ro_polynomial_fri_terminal_wp", 9, @{thm square_ro_polynomial_fri_terminal_wp}),
     ("square_ro_trace_fri_terminal_wp", 8, @{thm square_ro_trace_fri_terminal_wp}),
     ("square_ro_composition_fri_terminal_wp", 9, @{thm square_ro_composition_fri_terminal_wp})];
\<close>

end
