(*  License: BSD-3-Clause *)
theory RO_Honest_Verifier_Openings
 imports "Stark.RO_Honest_Verifier_Replay" "Stark.RO_Honest_Opening_Chunks"
begin

section \<open>Failure-Sensitive Honest Opening Checks\<close>

text \<open>Created-tree lookups give exact state-preserving authentication. The original absorbing verifier consumes honest query and FRI pair chunks and returns its actual fold expression. Matching successive committed polynomial values and composing the complete verifier remain separate obligations.\<close>

context merkle_tree
begin

lemma created_path_exact_wp:
  assumes ct: "created_tree xs tree s"
    and len: "length xs = 2^n"
    and idx: "i < length xs"
  shows "wp (check_authentication_path (length xs) i (xs!i)
    (get_authentication_path (length xs) i tree)) Q s = Q (Some (value tree,s))"
  using ct len idx
proof (induction n arbitrary: xs tree i Q)
  case 0
  then obtain x v where xs: "xs=[x]" and tree: "tree=Node Leaf v Leaf"
    and key: "fmlookup (HashMap s) x=Some v"
    by (cases xs; cases "tl xs") (auto simp: created_tree.simps)
  have i: "i=0" using "0.prems"(3) xs by simp
  show ?case by (simp add: xs tree i hash_known_wp[OF key])
next
  case (Suc n)
  let ?m = "2^n"
  have len: "length xs=2*?m" using Suc.prems(2) by simp
  have mid: "length xs div 2=?m" using len by simp
  obtain a b cs where xs: "xs=a#b#cs"
    using len by (cases xs; cases "tl xs") auto
  obtain l v r where tree: "tree=Node l v r"
    and lc: "created_tree (take ?m xs) l s"
    and rc: "created_tree (drop ?m xs) r s"
    and key: "fmlookup (HashMap s) (concat (value l) (value r))=Some v"
    using Suc.prems(1) unfolding xs
    by (auto simp: created_tree.simps Let_def mid[symmetric] xs)
  have llen: "length (take ?m xs)=2^n" and rlen: "length (drop ?m xs)=2^n"
    using len by simp_all
  show ?case
  proof (cases "i<?m")
    case True
    have bound: "i<length (take ?m xs)" using True llen by simp
    have leaf: "take ?m xs!i=xs!i" using True by simp
    have sub: "wp (check_authentication_path ?m i (xs!i)
      (get_authentication_path ?m i l)) Q' s=Q' (Some (value l,s))" for Q'
      using Suc.IH[OF lc llen bound, of Q'] by (simp only: llen leaf)
    show ?thesis
      by (simp add: tree len True wp_bind sub hash_known_wp[OF key])
  next
    case False
    have bound: "i-?m<length (drop ?m xs)" using Suc.prems(3) False len by simp
    have leaf: "drop ?m xs!(i-?m)=xs!i" using False len by simp
    have sub: "wp (check_authentication_path ?m (i-?m) (xs!i)
      (get_authentication_path ?m (i-?m) r)) Q' s=Q' (Some (value r,s))" for Q'
      using Suc.IH[OF rc rlen bound, of Q'] by (simp only: rlen leaf)
    show ?thesis
      by (simp add: tree len False wp_bind sub hash_known_wp[OF key])
  qed
qed

end

lemma protocol_created_path_exact_wp:
  fixes s :: "'f::finite protocol_channel"
  assumes ct: "protocol_created_tree xs tree sent"
    and len: "length xs=2^n"
    and idx: "i<length xs"
    and ext: "sent \<le> s"
  shows "wp (protocol_check_authentication_path (length xs) i (xs!i)
    (get_authentication_path (length xs) i tree)) Q s=Q (Some (value tree,s))"
proof -
  have ct': "protocol_created_tree xs tree s"
    by (rule protocol_created_tree_mono[OF ct ext])
  show ?thesis
    using protocol_merkle.created_path_exact_wp[
      OF ct'[unfolded protocol_created_tree_def], of n i Q] len idx
    by (simp add: protocol_check_authentication_path_def)
qed


context soundness
begin

lemma ro_query_decommitment_honest_wp:
  assumes ct: "protocol_created_tree xs tree sent"
    and len: "length xs=clength*scale"
    and pow: "length xs=2^n"
    and idx: "i<length xs"
    and path_len: "length (get_authentication_path (length xs) i tree)=floor_log (length xs)"
    and chain: "ro_absorb_lookup_chain sent (PState s) (honest_leaf_chunk xs tree i) final"
    and ext: "sent \<le> s"
    and tr: "PTranscript s=honest_leaf_chunk xs tree i @ rest"
  shows "wp (ro_query_decommitment_step (value tree) i) Q s =
    Q (Some (xs!i,s\<lparr>PState := final,PTranscript := rest\<rparr>))"
proof -
  let ?path = "get_authentication_path (length xs) i tree"
  let ?reads = "protocol_absorb_read \<bind> (\<lambda>v.
    ntimes protocol_absorb_read (floor_log (length xs)) \<bind> (\<lambda>ap. return (v,ap)))"
  let ?t = "s\<lparr>PState := final,PTranscript := rest\<rparr>"
  have reads: "wp ?reads F s=F (Some ((xs!i,?path),?t))" for F
    by (rule protocol_absorb_read_leaf_path_wp[OF chain[unfolded honest_leaf_chunk_def] ext
      tr[unfolded honest_leaf_chunk_def] path_len])
  have ext': "sent \<le> ?t" using ext by (simp add: less_eq_hash_ext_def)
  have auth: "wp (check_authentication_path (length xs) i (xs!i) ?path) F ?t =
    F (Some (value tree,?t))" for F
    unfolding check_authentication_path_def
    by (rule protocol_created_path_exact_wp[OF ct pow idx ext'])
  have factor: "ro_query_decommitment_step (value tree) i =
    (?reads \<bind> (\<lambda>(v,ap). check_authentication_path (length xs) i v ap \<bind>
       (\<lambda>root. assert (root=value tree) \<bind> (\<lambda>_. return v))))"
    unfolding ro_query_decommitment_step_def
    by (simp add: len mult.commute Let_def sm_bind_assoc)
  show ?thesis unfolding factor
    apply (subst wp_bind)
    apply (subst reads)
    by (simp add: wp_bind wp_return auth assert_def)
qed

lemma fri_layer_opening_finish_honest_wp:
  fixes sent s :: "'f protocol_channel"
  assumes ct: "protocol_created_tree xs tree sent"
    and len: "length xs=2^n"
    and idx: "i<length xs"
    and ext: "sent \<le> s"
  shows "wp (fri_layer_opening_finish b (value tree) i (xs!i) (length xs) pw
    (xs!i) (get_authentication_path (length xs) i tree)
    (xs!((i+length xs div 2) mod length xs))
    (get_authentication_path (length xs) ((i+length xs div 2) mod length xs) tree)) Q s =
    Q (Some ((i mod (length xs div 2),
      (xs!i + xs!((i+length xs div 2) mod length xs)) div 2 +
        b * ((xs!i - xs!((i+length xs div 2) mod length xs)) div (2*((h^i)*shift)^pw)),
      length xs div 2,pw+pw),s))"
proof -
  have pos: "0<length xs" using len by simp
  have sib: "(i+length xs div 2) mod length xs<length xs" by (rule mod_less_divisor[OF pos])
  have auth: "wp (check_authentication_path (length xs) j (xs!j)
    (get_authentication_path (length xs) j tree)) F s=F (Some (value tree,s))"
    if "j<length xs" for j F
    unfolding check_authentication_path_def
    by (rule protocol_created_path_exact_wp[OF ct len that ext])
  show ?thesis
    by (simp add: fri_layer_opening_finish_def wp_bind wp_return assert_def
      auth[OF idx] auth[OF sib])
qed


lemma ro_fri_layer_opening_honest_wp:
  assumes ct: "protocol_created_tree xs tree sent"
    and len: "length xs=2^n"
    and idx: "i<length xs"
    and paths: "\<And>j. length (get_authentication_path (length xs) j tree)=floor_log (length xs)"
    and chain: "ro_absorb_lookup_chain sent (PState s) (honest_fri_pair_chunk xs tree i) final"
    and ext: "sent \<le> s"
    and tr: "PTranscript s=honest_fri_pair_chunk xs tree i @ rest"
  shows "wp (ro_fri_layer_opening_step (b,value tree) (i,xs!i,length xs,pw)) Q s =
    Q (Some ((i mod (length xs div 2),
      (xs!i + xs!((i+length xs div 2) mod length xs)) div 2 +
        b * ((xs!i - xs!((i+length xs div 2) mod length xs)) div (2*((h^i)*shift)^pw)),
      length xs div 2,pw+pw),s\<lparr>PState := final,PTranscript := rest\<rparr>))"
proof -
  let ?j = "(i+length xs div 2) mod length xs"
  let ?p = "get_authentication_path (length xs) i tree"
  let ?q = "get_authentication_path (length xs) ?j tree"
  let ?reads = "protocol_absorb_read \<bind> (\<lambda>v.
    ntimes protocol_absorb_read (floor_log (length xs)) \<bind> (\<lambda>ap. return (v,ap)))"
  have chunk: "honest_fri_pair_chunk xs tree i=(xs!i # ?p) @ (xs!?j # ?q)"
    using idx by (simp add: honest_fri_pair_chunk_def honest_leaf_chunk_def Let_def)
  obtain mid where first: "ro_absorb_lookup_chain sent (PState s) (xs!i # ?p) mid"
    and second: "ro_absorb_lookup_chain sent mid (xs!?j # ?q) final"
    using chain by (auto simp: chunk ro_absorb_lookup_chain_append_iff)
  let ?t = "s\<lparr>PState := mid,PTranscript := (xs!?j # ?q)@rest\<rparr>"
  let ?u = "s\<lparr>PState := final,PTranscript := rest\<rparr>"
  have tr': "PTranscript s=(xs!i # ?p) @ ((xs!?j # ?q)@rest)" using tr chunk by simp
  have r1: "wp ?reads F s=F (Some ((xs!i,?p),?t))" for F
    by (rule protocol_absorb_read_leaf_path_wp[OF first ext tr' paths])
  have ext_t: "sent \<le> ?t" and ext_u: "sent \<le> ?u" using ext
    by (simp_all add: less_eq_hash_ext_def)
  have ch2: "ro_absorb_lookup_chain sent (PState ?t) (xs!?j # ?q) final"
    using second by simp
  have r2: "wp ?reads F ?t=F (Some ((xs!?j,?q),?u))" for F
    using protocol_absorb_read_leaf_path_wp[OF ch2 ext_t _ paths, of rest F]
    by simp
  have finish: "wp (fri_layer_opening_finish b (value tree) i (xs!i) (length xs) pw
    (xs!i) ?p (xs!?j) ?q) F ?u =
    F (Some ((i mod (length xs div 2),
      (xs!i+xs!?j) div 2 + b*((xs!i-xs!?j) div (2*((h^i)*shift)^pw)),
      length xs div 2,pw+pw),?u))" for F
    by (rule fri_layer_opening_finish_honest_wp[OF ct len idx ext_u])
  have factor: "ro_fri_layer_opening_step (b,value tree) (i,xs!i,length xs,pw)=
    (?reads \<bind> (\<lambda>(v,ap). ?reads \<bind> (\<lambda>(w,bp).
      fri_layer_opening_finish b (value tree) i (xs!i) (length xs) pw v ap w bp)))"
    by (simp add: ro_fri_layer_opening_step_def sm_bind_assoc)
  show ?thesis unfolding factor
    apply (subst wp_bind)
    apply (subst r1)
    apply (simp only: option.case prod.case)
    apply (subst wp_bind)
    apply (subst r2)
    by (simp add: finish)
qed


lemma ro_query_decommitments_honest_wp:
  assumes ct: "protocol_created_tree xs tree sent"
    and len: "length xs=clength*scale"
    and pow: "length xs=2^n"
    and indices: "\<And>i. i\<in>set positions \<Longrightarrow> i<length xs"
    and paths: "\<And>i. length (get_authentication_path (length xs) i tree)=floor_log (length xs)"
    and chain: "ro_absorb_lookup_chain sent (PState s)
      (List.concat (map (honest_leaf_chunk xs tree) positions)) final"
    and ext: "sent \<le> s"
    and tr: "PTranscript s=List.concat (map (honest_leaf_chunk xs tree) positions)@rest"
  shows "wp (mmap (map (ro_query_decommitment_step (value tree)) positions)) Q s =
    Q (Some (map (\<lambda>i. xs!i) positions,s\<lparr>PState := final,PTranscript := rest\<rparr>))"
  using indices chain ext tr
proof (induction positions arbitrary: s Q)
  case Nil
  then show ?case by (auto simp: wp_return)
next
  case (Cons i positions)
  let ?chunk = "honest_leaf_chunk xs tree i"
  let ?tail = "List.concat (map (honest_leaf_chunk xs tree) positions)"
  obtain mid where first: "ro_absorb_lookup_chain sent (PState s) ?chunk mid"
    and second: "ro_absorb_lookup_chain sent mid ?tail final"
    using Cons.prems(2) by (auto simp: ro_absorb_lookup_chain_append_iff)
  let ?t = "s\<lparr>PState := mid,PTranscript := ?tail@rest\<rparr>"
  have idx: "i<length xs" by (rule Cons.prems(1)) simp
  have tr: "PTranscript s=?chunk @ (?tail@rest)" using Cons.prems(4) by simp
  have head: "wp (ro_query_decommitment_step (value tree) i) F s =
    F (Some (xs!i,?t))" for F
    by (rule ro_query_decommitment_honest_wp[OF ct len pow idx paths first Cons.prems(3) tr])
  have ext: "sent \<le> ?t" using Cons.prems(3) by (simp add: less_eq_hash_ext_def)
  have tail: "wp (mmap (map (ro_query_decommitment_step (value tree)) positions)) F ?t =
    F (Some (map (\<lambda>i. xs!i) positions,s\<lparr>PState := final,PTranscript := rest\<rparr>))" for F
    using Cons.IH[OF _ _ ext, of F] Cons.prems(1) second by simp
  show ?case by (simp add: wp_bind wp_return head tail)
qed

lemma ro_check_decommit_on_query_honest_wp:
  assumes ct: "protocol_created_tree xs tree sent"
    and len: "length xs=clength*scale"
    and pow: "length xs=2^n"
    and indices: "\<And>i. i\<in>set (powers_scaled idx) \<Longrightarrow> i<length xs"
    and paths: "\<And>i. length (get_authentication_path (length xs) i tree)=floor_log (length xs)"
    and chain: "ro_absorb_lookup_chain sent (PState s) (honest_query_chunk xs tree idx) final"
    and ext: "sent \<le> s"
    and tr: "PTranscript s=honest_query_chunk xs tree idx@rest"
  shows "wp (mmap (ro_check_decommit_on_query (value tree) idx)) Q s =
    Q (Some (map (\<lambda>i. xs!i) (powers_scaled idx),s\<lparr>PState := final,PTranscript := rest\<rparr>))"
  unfolding ro_check_decommit_on_query_def
  by (rule ro_query_decommitments_honest_wp[OF ct len pow indices paths
    chain[unfolded honest_query_chunk_def] ext tr[unfolded honest_query_chunk_def]])

end

end
