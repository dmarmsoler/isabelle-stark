(*  Title:      Stark/RO_Honest_Opening_Chunks.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory RO_Honest_Opening_Chunks
 imports "Stark.RO_Honest_Composition_Reconstruction"
begin

section \<open>Honest Merkle Openings and Query Chunks\<close>

text \<open>Constructed trees for one word are unique in one oracle map, without collision freedom. Honest authentication is proved separately from the checked builder's serialization predicate. FRI pairs use the original modulo locations and no terminal-layer opening.\<close>

context merkle_tree
begin

lemma created_tree_unique:
  assumes "created_tree xs t s" "created_tree xs u s"
  shows "t=u"
  using assms
  apply (induction xs t s arbitrary: u rule: created_tree.induct)
  apply (auto simp: created_tree.simps Let_def)
  by fastforce

end

lemma protocol_created_tree_unique:
  assumes "protocol_created_tree xs t s" "protocol_created_tree xs u s"
  shows "t=u"
  using assms unfolding protocol_created_tree_def
  by (rule protocol_merkle.created_tree_unique)

context soundness
begin

lemma hash_only_ro_single_hash: "hash_only_ro 1 (hash x)"
proof -
  have "hash_only_ro (Suc 0) (hash x \<bind> (\<lambda>y. return y))"
    by (rule hash_only_ro.Ask) (rule hash_only_ro.Pure)
  then show ?thesis by simp
qed

lemma hash_only_ro_authentication_path:
  "hash_only_ro (Suc (length path))
    (protocol_merkle.check_authentication_path len idx leaf path)"
proof (induction path arbitrary: len idx leaf)
  case Nil
  show ?case using hash_only_ro_single_hash[of leaf] by simp
next
  case (Cons x path)
  have h: "hash_only_ro (Suc (length path) + 1)
    (protocol_merkle.check_authentication_path len idx leaf path \<bind> (\<lambda>v. hash (f v)))"
    for len idx leaf f
    by (rule hash_only_ro_bind[OF Cons.IH]) (rule hash_only_ro_single_hash)
  show ?case using h by simp
qed

lemma protocol_honest_path_authenticates:
  fixes s :: "'f protocol_channel"
  assumes ct: "protocol_created_tree xs tree s0"
    and len: "length xs=2^n"
    and idx: "idx<length xs"
    and ext: "s0\<le>s"
  shows "wp_event
    (protocol_check_authentication_path (length xs) idx (xs!idx)
      (get_authentication_path (length xs) idx tree))
    (\<lambda>out. case out of None \<Rightarrow> False | Some (r,_) \<Rightarrow> r=value tree) s=1"
proof -
  have nf: "None \<notin> dom (dist (execute
    (protocol_merkle.check_authentication_path (length xs) idx (MerkleLeaf (xs!idx))
      (get_authentication_path (length xs) idx tree)) s))"
    by (rule hash_only_ro_no_failure[OF hash_only_ro_authentication_path])
  show ?thesis
    unfolding protocol_check_authentication_path_def
    using protocol_merkle.check_created_tree[OF ct[unfolded protocol_created_tree_def],
      of n idx "MerkleLeaf (xs!idx)" s] len idx ext nf by simp
qed

lemma protocol_created_path_length:
  assumes out: "Some (tree,t) \<in> set_dist (execute (protocol_create xs) s)"
    and ne: "xs \<noteq> []"
  shows "length (get_authentication_path (length xs) idx tree)=floor_log (length xs)"
  using protocol_merkle.create_get_authentication_path_len[OF out[unfolded protocol_create_def]]
    ne by simp

definition honest_leaf_chunk where
  "honest_leaf_chunk xs tree idx = xs!idx # get_authentication_path (length xs) idx tree"

definition honest_query_chunk where
  "honest_query_chunk xs tree idx =
    List.concat (map (honest_leaf_chunk xs tree) (powers_scaled idx))"

definition honest_fri_pair_chunk where
  "honest_fri_pair_chunk xs tree idx =
    (let j=idx mod length xs; k=(j+length xs div 2) mod length xs in
     honest_leaf_chunk xs tree j @ honest_leaf_chunk xs tree k)"

fun honest_fri_chunks where
  "honest_fri_chunks [] idx = []"
| "honest_fri_chunks ((xs,tree)#rest) idx =
    honest_fri_pair_chunk xs tree idx #
      honest_fri_chunks rest (idx mod length xs)"

lemma honest_query_chunk_format:
  assumes len: "length xs=clength*scale"
    and paths: "\<And>j. length (get_authentication_path (length xs) j tree)=floor_log (length xs)"
  shows "query_decommitment_transcript idx
    (map (\<lambda>j. xs!j) (powers_scaled idx))
    (map (\<lambda>j. get_authentication_path (length xs) j tree) (powers_scaled idx))
    (honest_query_chunk xs tree idx)"
  unfolding query_decommitment_transcript_def honest_query_chunk_def honest_leaf_chunk_def
  using paths
  by (simp add: len[symmetric] zip_map_map zip_same_conv_map o_def)

lemma honest_fri_pair_chunk_format:
  assumes paths: "\<And>j. length (get_authentication_path (length xs) j tree)=floor_log (length xs)"
  shows "fri_layer_opening_chunk (length xs)
    (xs!(idx mod length xs)) (get_authentication_path (length xs) (idx mod length xs) tree)
    (xs!((idx mod length xs+length xs div 2) mod length xs))
    (get_authentication_path (length xs) ((idx mod length xs+length xs div 2) mod length xs) tree)
    (honest_fri_pair_chunk xs tree idx)"
  by (simp add: fri_layer_opening_chunk_def honest_fri_pair_chunk_def honest_leaf_chunk_def paths Let_def)

lemma honest_fri_chunks_length:
  "length (honest_fri_chunks pairs idx)=length pairs"
  by (induction pairs arbitrary: idx) (auto split: prod.splits)

lemma honest_fri_chunks_format:
  assumes lens: "map (length \<circ> fst) pairs=fri_layer_lengths n len"
    and paths: "\<And>xs tree j. (xs,tree) \<in> set pairs \<Longrightarrow>
      length (get_authentication_path (length xs) j tree)=floor_log (length xs)"
  shows "fri_layers_transcript n len (honest_fri_chunks pairs idx)
    (List.concat (honest_fri_chunks pairs idx))"
  using lens paths
proof (induction pairs arbitrary: n len idx)
  case Nil
  then show ?case by (cases n) (auto simp: fri_layers_transcript_def)
next
  case (Cons pair pairs)
  obtain xs tree where pair: "pair=(xs,tree)" by (cases pair) auto
  obtain m where n: "n=Suc m" using Cons.prems(1) by (cases n) auto
  have xlen: "length xs=len" and tail: "map (length \<circ> fst) pairs=fri_layer_lengths m (len div 2)"
    using Cons.prems(1) by (simp_all add: pair n o_def)
  have local_paths: "length (get_authentication_path (length xs) j tree)=floor_log (length xs)" for j
    by (rule Cons.prems(2)) (simp add: pair)
  have first: "\<exists>xp xp_path xn xn_path. fri_layer_opening_chunk len xp xp_path xn xn_path
    (honest_fri_pair_chunk xs tree idx)"
    using honest_fri_pair_chunk_format[OF local_paths, of idx] xlen by blast
  have rest: "fri_layers_transcript m (len div 2)
    (honest_fri_chunks pairs (idx mod length xs))
    (List.concat (honest_fri_chunks pairs (idx mod length xs)))"
    by (rule Cons.IH[OF tail]) (use Cons.prems(2) in auto)
  show ?case using first rest
    by (simp add: pair n fri_layers_transcript_def)
qed

lemma fri_layer_lengths_nth_div:
  assumes "j<n"
  shows "fri_layer_lengths n len!j=len div 2^j"
  using assms
proof (induction n arbitrary: len j)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have div: "len div 2 div 2^k=len div (2*2^k)" for k
    using div_mult2_eq'[of len 2 "2^k"] by simp
  show ?case using Suc by (cases j) (auto simp: div)
qed

lemma honest_round_chunk_format:
  assumes len: "length xs=clength*scale"
    and base: "\<And>j. length (get_authentication_path (length xs) j tree)=floor_log (length xs)"
    and tlens: "map (length \<circ> fst) tp=fri_layer_lengths (length trs) (clength*scale)"
    and clens: "map (length \<circ> fst) cps=fri_layer_lengths (length crs) (clength*scale)"
    and tpaths: "\<And>ys tr j. (ys,tr)\<in>set tp \<Longrightarrow>
      length (get_authentication_path (length ys) j tr)=floor_log (length ys)"
    and cpsaths: "\<And>ys tr j. (ys,tr)\<in>set cps \<Longrightarrow>
      length (get_authentication_path (length ys) j tr)=floor_log (length ys)"
  shows "verifier_query_round_chunk idx trs crs
    (honest_query_chunk xs tree idx @ List.concat (honest_fri_chunks tp idx) @
      List.concat (honest_fri_chunks cps idx))"
  unfolding verifier_query_round_chunk_def
  using honest_query_chunk_format[OF len base, of idx]
    honest_fri_chunks_format[OF tlens tpaths, of idx]
    honest_fri_chunks_format[OF clens cpsaths, of idx]
  by blast

fun honest_create_trees where
  "honest_create_trees [] = return []"
| "honest_create_trees (xs#xss) =
    (protocol_create xs \<bind> (\<lambda>tree.
     honest_create_trees xss \<bind> (\<lambda>rest. return ((xs,tree)#rest))))"

lemma honest_create_trees_hash_only:
  "hash_only_ro (sum_list (map (\<lambda>xs. 2*length xs-1) xss))
    (honest_create_trees xss)"
proof (induction xss)
  case Nil
  then show ?case by (simp add: hash_only_ro.Pure)
next
  case (Cons xs xss)
  show ?case by (simp only: honest_create_trees.simps list.map sum_list.Cons)
    (rule hash_only_ro_bind[OF hash_only_ro_protocol_create hash_only_ro_map[OF Cons.IH]])
qed

lemma honest_create_trees_outcome:
  assumes out: "Some (pairs,t)\<in>set_dist (execute (honest_create_trees xss) s)"
  shows "s\<le>t \<and> map fst pairs=xss \<and>
    (\<forall>xs tree. (xs,tree)\<in>set pairs \<longrightarrow> protocol_created_tree xs tree t \<and>
      (xs\<noteq>[] \<longrightarrow> (\<forall>j. length (get_authentication_path (length xs) j tree)=floor_log (length xs))))"
  using out
proof (induction xss arbitrary: pairs s t)
  case Nil
  then show ?case by (simp add: hash_ext_refl)
next
  case (Cons xs xss)
  obtain tree u rest where
    head: "Some (tree,u)\<in>set_dist (execute (protocol_create xs) s)"
    and tail: "Some (rest,t)\<in>set_dist (execute (honest_create_trees xss) u)"
    and pairs: "pairs=(xs,tree)#rest"
    using Cons.prems by (auto elim!: set_dist_bindE split: prod.splits)
  have su: "s\<le>u" and ct: "protocol_created_tree xs tree u"
    using protocol_create_outcome[OF head] by auto
  note ih=Cons.IH[OF tail]
  have ct': "protocol_created_tree xs tree t"
    by (rule protocol_created_tree_mono[OF ct]) (use ih in auto)
  show ?case using ih ct' protocol_created_path_length[OF head] hash_ext_trans[OF su]
    by (auto simp: pairs)
qed

lemma honest_trees_match_roots:
  fixes t :: "'f protocol_channel"
  assumes words: "map fst pairs=xss"
    and len: "length roots=length xss"
    and committed: "\<And>j. j<length roots \<Longrightarrow> \<exists>tree.
      protocol_created_tree (xss!j) tree t \<and> value tree=roots!j"
    and built: "\<And>xs tree. (xs,tree)\<in>set pairs \<Longrightarrow> protocol_created_tree xs tree t"
  shows "map (value \<circ> snd) pairs=roots"
proof (rule nth_equalityI)
  show "length (map (value \<circ> snd) pairs)=length roots" using words len by (metis length_map)
  fix j
  assume j: "j<length (map (value \<circ> snd) pairs)"
  have jp: "j<length pairs" and jr: "j<length roots" using j words len by (auto dest: arg_cong[where f=length])
  have pair: "(fst (pairs!j),snd (pairs!j))\<in>set pairs" using nth_mem[OF jp] by simp
  have word: "fst (pairs!j)=xss!j" using words jp by (metis nth_map)
  have ct: "protocol_created_tree (xss!j) (snd (pairs!j)) t" using built[OF pair] word by simp
  obtain tree where tree: "protocol_created_tree (xss!j) tree t" "value tree=roots!j"
    using committed[OF jr] by blast
  have "snd (pairs!j)=tree" by (rule protocol_created_tree_unique[OF ct tree(1)])
  then show "map (value \<circ> snd) pairs!j=roots!j" using jp tree(2) by simp
qed

lemma protocol_honest_fri_pair_authenticates:
  fixes s :: "'f protocol_channel"
  assumes ct: "protocol_created_tree xs tree s0"
    and len: "length xs=2^n"
    and ext: "s0\<le>s"
  shows "wp_event
    (protocol_check_authentication_path (length xs) (idx mod length xs)
      (xs!(idx mod length xs)) (get_authentication_path (length xs) (idx mod length xs) tree))
    (\<lambda>out. case out of None \<Rightarrow> False | Some (r,_) \<Rightarrow> r=value tree) s=1"
    "wp_event
    (protocol_check_authentication_path (length xs) ((idx mod length xs+length xs div 2) mod length xs)
      (xs!((idx mod length xs+length xs div 2) mod length xs))
      (get_authentication_path (length xs) ((idx mod length xs+length xs div 2) mod length xs) tree))
    (\<lambda>out. case out of None \<Rightarrow> False | Some (r,_) \<Rightarrow> r=value tree) s=1"
  by (rule protocol_honest_path_authenticates[OF ct len _ ext]; simp add: len)+

end
end
