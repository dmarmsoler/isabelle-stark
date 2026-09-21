(* Title: Stark/Soundness_FRI_Weighted_Challenge_Completion.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Challenge_Completion
  imports
    "Soundness_FRI_Weighted_Semantic_Endpoint"
    "Stark.Soundness_FRI_Correlated_Agreement_Actual_Query"
begin

section \<open>Challenge Completion for weighted MCA soundness\<close>

text \<open>Recover actual FRI challenge keys and average only their unrevealed answers. Cached values, exceptional updates and the exact modulo-preimage mass bound remain explicit.\<close>

subsection \<open>Combined FRI Challenge facts\<close>

text \<open>Bounded applicability facts. Averaging lemmas below are not yet
a challenge-aware adaptive-family or original-experiment theorem.\<close>

lemma cfa_latent_initial:
 fixes S :: "'b::finite \<Rightarrow> 'a::finite set"
 assumes mass: "\<And>b. lpw_mass (S b)\<le>p"
 shows "lpw_mean (\<lambda>b. lpw_score (S b) p (\<lambda>k x. None) (\<lambda>k. None) n i v)\<le>p^n"
proof -
 have "lpw_mean (\<lambda>b. lpw_score (S b) p (\<lambda>k x. None) (\<lambda>k. None) n i v)
   \<le>lpw_mean (\<lambda>b::'b. p^n)"
   by (rule lpw_mean_mono) (rule lpw_score_initial[OF mass])
 then show ?thesis by simp
qed

lemma cfa_latent_query_average:
 fixes S :: "'b::finite \<Rightarrow> 'a::finite set"
 assumes fresh: "X(k,w)=None"
 shows "lpw_mean (\<lambda>x. lpw_mean (\<lambda>b.
   lpw_score (S b) p D (X((k,w):=Some x)) n i v))=
   lpw_mean (\<lambda>b. lpw_score (S b) p D X n i v)"
 by (subst lpw_mean_swap) (simp only: lpw_score_fresh_average[where X=X and k=k and w=w, OF fresh])

context soundness
begin

lemma cfa_header_challenge_fields:
 "as_header M start (data\<lparr>staged_trace_fri_challenges:=bs\<rparr>)=as_header M start data"
 "as_header M start (data\<lparr>staged_composition_fri_challenges:=bs\<rparr>)=as_header M start data"
 by (simp_all add: as_header_def weighted_semantic_header_shape_def weighted_semantic_header_def)

lemma cfa_header_challenge_update:
 "as_header (fmupd (TraceFriChallenge i v) b M) start data=as_header M start data"
 "as_header (fmupd (CompositionFriChallenge i v) b M) start data=as_header M start data"
 by (simp_all add: as_header_def)

lemma cfa_trace_chain_drop:
 "ro_absorb_lookup_chain (channel_for_hash_map (fmdrop (TraceFriChallenge i v) M)) st xs final =
  ro_absorb_lookup_chain (channel_for_hash_map M) st xs final"
 unfolding channel_for_hash_map_def
 by (induction xs arbitrary: st) simp_all

lemma cfa_header_trace_drop:
 "as_header (fmdrop (TraceFriChallenge i v) M) start data=as_header M start data"
 by (simp add: as_header_def cfa_trace_chain_drop)

lemma cfa_trace_evidence_missing:
 assumes chain: "ro_absorb_lookup_chain (channel_for_hash_map M)
   (PState adversary_initial_state) (fr#take (Suc i) roots) v"
   and i: "i<length roots" and missing: "fmlookup M (TraceFriChallenge i v)=None"
 shows "\<not>ro_conditioned_trace_challenge_evidence M fr roots bs"
proof
 assume ev: "ro_conditioned_trace_challenge_evidence M fr roots bs"
 obtain w where w: "ro_absorb_lookup_chain (channel_for_hash_map M)
   (PState adversary_initial_state) (fr#take (Suc i) roots) w"
   and lookup: "fmlookup M (TraceFriChallenge i w)=Some(bs!i)"
   using ev i unfolding ro_conditioned_trace_challenge_evidence_def by blast
 have "v=w" by (rule ro_absorb_lookup_chain_functional[OF chain w])
 then show False using missing lookup by simp
qed

lemma cfa_header_without_trace_evidence:
 assumes header: "as_header M start data"
   and chain: "ro_absorb_lookup_chain (channel_for_hash_map M)
     (PState adversary_initial_state) (staged_trace_root data#
       take (Suc i) (staged_trace_fri_roots data)) v"
   and i: "i<length (staged_trace_fri_roots data)"
 shows "as_header (fmdrop (TraceFriChallenge i v) M) start data"
   "\<not>ro_conditioned_trace_challenge_evidence (fmdrop (TraceFriChallenge i v) M)
       (staged_trace_root data) (staged_trace_fri_roots data) bs"
proof -
 show "as_header (fmdrop (TraceFriChallenge i v) M) start data"
   using header by (simp add: cfa_header_trace_drop)
 have old: "ro_absorb_lookup_chain (channel_for_hash_map (fmdrop (TraceFriChallenge i v) M))
     (PState adversary_initial_state) (staged_trace_root data#
       take (Suc i) (staged_trace_fri_roots data)) v"
   using chain
   by (simp only: cfa_trace_chain_drop)
 show "\<not>ro_conditioned_trace_challenge_evidence (fmdrop (TraceFriChallenge i v) M)
       (staged_trace_root data) (staged_trace_fri_roots data) bs"
   by (rule cfa_trace_evidence_missing[OF old i]) simp
qed

lemma cfa_branch_mass:
 "lpw_mass (query_index_raw_preimage
   (fri_mca_residual_query_indices N r is_trace prefix prefix_state data s))
  \<le> nnreal (query_raw_preimage_card_envelope (fri_mca_residual_branch_bound r is_trace))/nnreal size"
proof -
 let ?I="fri_mca_residual_query_indices N r is_trace prefix prefix_state data s"
 have card: "card(query_index_raw_preimage ?I)\<le>
   query_raw_preimage_card_envelope (fri_mca_residual_branch_bound r is_trace)"
   by (rule order_trans[OF card_query_index_raw_preimage_le_query_envelope[
       OF fri_mca_residual_query_indices_subset]
       query_raw_preimage_card_envelope_mono[OF fri_mca_residual_query_indices_card]])
 show ?thesis unfolding lpl_mass_eq ep_mass_def
   by (rule nnreal_nat_divide_right_mono[OF card])
qed

lemma cfa_branch_frozen:
 assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
   and nt: "\<not>hash_map_new_output_hit (weighted_semantic_interval_targets M)
     (channel_for_hash_map M) (channel_for_hash_map U)"
   and header: "as_header M start data"
 shows "fri_mca_residual_query_lists N r is_trace prefix prefix_state data
     (channel_for_hash_map U)=
   fri_mca_residual_query_lists N r is_trace prefix prefix_state data
     (channel_for_hash_map M)"
proof -
 obtain rest where chain: "ro_absorb_lookup_chain (channel_for_hash_map M)
   (PState adversary_initial_state) (weighted_semantic_header data@rest) start"
   using header unfolding as_header_def by blast
 have messages: "set(weighted_semantic_header data)\<subseteq>transcript_absorb_message_values M"
   using ro_absorb_lookup_chain_messages_subset[OF chain] by auto
 have sub: "fri_checked_builder_merkle_targets data (channel_for_hash_map M)
   \<subseteq>weighted_semantic_interval_targets M"
   using messages unfolding fri_checked_builder_merkle_targets_def
     merkle_prefix_path_targets_def weighted_semantic_interval_targets_def
     weighted_semantic_header_def verifier_header_messages_def by auto
 have no: "\<not>hash_map_new_output_hit
     (fri_checked_builder_merkle_targets data (channel_for_hash_map M))
     (channel_for_hash_map M) (channel_for_hash_map U)"
   using hash_map_new_output_hit_subset[OF sub] nt by blast
 show ?thesis by (rule fri_mca_residual_query_lists_stable[OF ext no])
qed


end

subsection \<open>Complete Initial Target facts\<close>

context soundness
begin

lemma cita_target_map:
 fixes m :: "('a, 'f protocol_channel) state_monad"
 shows "wp_event (m \<bind> (\<lambda>x. return (f x))) (hash_new_output_hit_event B a) s =
   wp_event m (hash_new_output_hit_event B a) s"
 unfolding wp_event_def wp_bind_return_map
 apply (rule arg_cong[where f="\<lambda>P. wp m P s"], rule ext)
 subgoal for out
   by (cases out) (auto simp: hash_new_output_hit_event_def split: prod.splits)
 done

lemma cita_witness_target_probability:
 "wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
    (hash_new_output_hit_event B a) s =
  wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
    (hash_new_output_hit_event B a) s"
proof -
 have x: "wp_event (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
    (hash_new_output_hit_event B a) s =
  wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
    (hash_new_output_hit_event B a) s"
   using cita_target_map[where m="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A"
     and f="\<lambda>(((prefix_with_state,data,query_start,raws,query_states),attacker_state),result).
       (((data,query_start,raws,query_states),attacker_state),result)"
     and B=B and a=a and s=s]
   by (simp only: split_def ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection_all_rounds[unfolded split_def])
 have y: "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
    (hash_new_output_hit_event B a) s =
  wp_event (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
    (hash_new_output_hit_event B a) s"
   using cita_target_map[where m="ro_absorb_checked_staged_security_experiment_with_query_witnesses A"
     and f="\<lambda>(((data,query_start,raws,query_states),attacker_state),result).
       ((data,attacker_state),result)"
     and B=B and a=a and s=s]
   by (simp only: split_def ro_absorb_checked_staged_security_experiment_with_query_witnesses_projection[unfolded split_def])
 show ?thesis using x y by simp
qed

lemma cita_final_initial_bound:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
 shows "wp_event
   (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
   (hash_new_output_hit_event {PState adversary_initial_state} adversary_initial_state)
   adversary_initial_state \<le>
   nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)/nnreal size"
proof -
 have target: "hash_target_program {PState adversary_initial_state}
   (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
   (ro_absorb_checked_staged_security_experiment_with_data_state A)"
   by (rule hash_target_program_ro_absorb_checked_staged_security_experiment_with_data_state[OF wf controlled])
 have bound: "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
     (hash_new_output_hit_event {PState adversary_initial_state} adversary_initial_state)
     adversary_initial_state \<le>
     hash_target_budget_value {PState adversary_initial_state}
       (ro_absorb_checked_staged_security_hash_query_budget_for budgets)"
   using target unfolding hash_target_program_def hash_target_budget_def by blast
 show ?thesis using bound
   by (simp add: cita_witness_target_probability hash_target_budget_value_def)
qed

lemma cita_initial_guard_exact:
 "\<not>hash_new_output_hit_event {PState adversary_initial_state}
    adversary_initial_state (Some(x,t)) \<longleftrightarrow>
  PState adversary_initial_state\<notin>hash_map_output_values t"
 by (auto simp: hash_new_output_hit_event_def hash_map_new_output_hit_def
   hash_map_output_values_def adversary_initial_state_def)

lemma cita_semantic_guard_split:
 assumes hit:
   "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
     (ro_mca_decoded_semantic_query_lists rT rC) out"
 shows "final_hash_collision_event out \<or>
   hash_new_output_hit_event {PState adversary_initial_state} adversary_initial_state out \<or>
   ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit out \<or>
   ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit out \<or>
   vr_clean_semantic_event rT rC out"
proof -
 obtain prefix prefix_state data query_start raws query_states attacker_state result u where
   out: "out=Some (((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),result),u)"
   using hit unfolding
     ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
   by (cases out) (auto split: prod.splits)
 have guarded: "vr_clean_semantic_event rT rC out \<longleftrightarrow>
   \<not>hash_map_output_collision u \<and>
   PState adversary_initial_state\<notin>hash_map_output_values u \<and>
   \<not>hash_map_new_output_hit
     (first_trace_fri_root_prefix_merkle_targets prefix prefix_state) prefix_state u \<and>
   \<not>hash_map_new_output_hit
     (ro_actual_query_composition_prefix_targets data query_start) query_start u"
   using hit unfolding out vr_original_event_guarded_iff by simp
 show ?thesis
   using guarded cita_initial_guard_exact[of _ u]
   unfolding out
     ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_def
     ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_def
     ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
     final_hash_collision_event_def
   by force
qed


end

subsection \<open>Latent Challenge Average\<close>

text \<open>Proof-side completion of a fixed finite list of oracle keys.
Cached values are retained; distinctness is required for fresh-key resolution.\<close>

fun lca_avg :: "'k list \<Rightarrow> ('k \<Rightarrow> 'a::finite option) \<Rightarrow>
  ('a list \<Rightarrow> prob) \<Rightarrow> prob" where
 "lca_avg [] C f = f []"
| "lca_avg (k#ks) C f = (case C k of
    None \<Rightarrow> lpw_mean (\<lambda>x. lca_avg ks C (\<lambda>bs. f (x#bs)))
  | Some x \<Rightarrow> lca_avg ks C (\<lambda>bs. f (x#bs)))"

lemma lca_avg_mono:
 assumes "\<And>bs. f bs\<le>g bs"
 shows "lca_avg ks C f\<le>lca_avg ks C g"
 using assms
 by (induction ks arbitrary: f g) (auto intro: lpw_mean_mono split: option.splits)

lemma lca_avg_cong:
 "(\<And>bs. f bs=g bs) \<Longrightarrow> lca_avg ks C f=lca_avg ks C g"
  by (rule arg_cong[where f="lca_avg ks C"], rule ext)

lemma lca_avg_const [simp]: "lca_avg ks C (\<lambda>bs. c)=c"
 by (induction ks) (simp_all split: option.splits)

lemma lca_avg_lookup_cong:
 assumes "\<And>k. k\<in>set ks \<Longrightarrow> C k=D k"
 shows "lca_avg ks C f=lca_avg ks D f"
 using assms
proof (induction ks arbitrary: f)
 case Nil then show ?case by simp
next
 case (Cons k ks)
 have head: "C k=D k" by (rule Cons.prems) simp
 have tail: "\<And>x. lca_avg ks C (\<lambda>bs. f(x#bs))=
   lca_avg ks D (\<lambda>bs. f(x#bs))"
   by (rule Cons.IH) (use Cons.prems in auto)
 show ?case by (simp only: lca_avg.simps head tail)
qed

lemma lca_avg_update_irrelevant:
 "k\<notin>set ks \<Longrightarrow> lca_avg ks (C(k:=Some z)) f=lca_avg ks C f"
 by (rule lca_avg_lookup_cong) auto

lemma lca_avg_swap:
 "lpw_mean (\<lambda>x. lca_avg ks C (f x))=
  lca_avg ks C (\<lambda>bs. lpw_mean (\<lambda>x. f x bs))"
proof (induction ks arbitrary: f)
 case Nil then show ?case by simp
next
 case (Cons k ks)
 show ?case
 proof (cases "C k")
  case None
  show ?thesis
   unfolding lca_avg.simps None option.case
   apply (subst lpw_mean_swap)
   by (simp only: Cons.IH)
 next
  case (Some x)
  show ?thesis by (simp only: lca_avg.simps Some option.case Cons.IH)
 qed
qed

lemma lca_avg_fresh_member:
 assumes distinct: "distinct ks" and member: "k\<in>set ks" and fresh: "C k=None"
 shows "lpw_mean (\<lambda>z. lca_avg ks (C(k:=Some z)) f)=lca_avg ks C f"
 using distinct member
proof (induction ks arbitrary: f)
 case Nil then show ?case by simp
next
 case (Cons a ks)
 show ?case
 proof (cases "k=a")
  case True
  have outside: "k\<notin>set ks" using Cons.prems True by simp
  have head: "\<And>z. (C(k:=Some z)) a=Some z" using True by simp
  have before: "C a=None" using fresh True by simp
  have tail: "\<And>z. lca_avg ks (C(k:=Some z)) (\<lambda>bs. f(z#bs))=
    lca_avg ks C (\<lambda>bs. f(z#bs))"
   by (rule lca_avg_update_irrelevant[OF outside])
  show ?thesis
      by (simp only: lca_avg.simps head before option.case tail)
 next
  case False
  have tail: "\<And>x. lpw_mean (\<lambda>z. lca_avg ks (C(k:=Some z)) (\<lambda>bs. f(x#bs)))=
    lca_avg ks C (\<lambda>bs. f(x#bs))"
   by (rule Cons.IH) (use Cons.prems False in auto)
  have head: "\<And>z. (C(k:=Some z)) a=C a" using False by simp
  show ?thesis
  proof (cases "C a")
   case None
   show ?thesis
    unfolding lca_avg.simps head None option.case
    by (subst lpw_mean_swap) (simp only: tail)
  next
   case (Some x)
   show ?thesis by (simp only: lca_avg.simps head Some option.case tail)
  qed
 qed
qed

lemma lca_avg_fresh_update:
 assumes "distinct ks" "C k=None"
 shows "lpw_mean (\<lambda>z. lca_avg ks (C(k:=Some z)) f)=lca_avg ks C f"
proof (cases "k\<in>set ks")
 case True show ?thesis by (rule lca_avg_fresh_member[where C=C and k=k, OF assms(1) True assms(2)])
next
 case False
 show ?thesis
    by (simp only: lca_avg_update_irrelevant[OF False] lpw_mean_const)
qed

lemma lca_avg_cached_update:
 "C k=Some z \<Longrightarrow> lca_avg ks (C(k:=Some z)) f=lca_avg ks C f"
  by (rule lca_avg_lookup_cong) auto

lemma lca_avg_resolved:
 assumes "\<And>k. k\<in>set ks \<Longrightarrow> C k=Some(A k)"
 shows "lca_avg ks C f=f(map A ks)"
 using assms
proof (induction ks arbitrary: f)
 case Nil then show ?case by simp
next
 case (Cons k ks)
 have head: "C k=Some(A k)" by (rule Cons.prems) simp
 have tail: "lca_avg ks C (\<lambda>bs. f(A k#bs))=f(A k#map A ks)"
   by (rule Cons.IH) (use Cons.prems in auto)
 show ?case by (simp only: lca_avg.simps head option.case tail list.map)
qed

subsection \<open>Latent Challenge Keys\<close>

context soundness
begin

definition lck_endpoint where
 "lck_endpoint M xs=(SOME v. ro_absorb_lookup_chain (channel_for_hash_map M)
   (PState adversary_initial_state) xs v)"

lemma lck_endpoint_eq:
 "ro_absorb_lookup_chain (channel_for_hash_map M) (PState adversary_initial_state) xs v
  \<Longrightarrow> lck_endpoint M xs=v"
 unfolding lck_endpoint_def
 by (rule some_equality) (assumption, erule ro_absorb_lookup_chain_functional)

definition lck_trace_keys where
 "lck_trace_keys M data=map (\<lambda>i. TraceFriChallenge i
   (lck_endpoint M (staged_trace_root data#take (Suc i) (staged_trace_fri_roots data))))
   [0..<length(staged_trace_fri_roots data)]"

definition lck_composition_keys where
 "lck_composition_keys M data=map (\<lambda>i. CompositionFriChallenge i
   (lck_endpoint M (composition_fri_challenge_prefix_messages
    (staged_trace_root data) (staged_trace_fri_roots data) (staged_trace_final data)
    (staged_alphas data) (staged_degree data) (staged_composition_fri_roots data) i)))
   [0..<length(staged_composition_fri_roots data)]"

definition lck_keys where
 "lck_keys M data=lck_trace_keys M data@lck_composition_keys M data"

lemma lck_distinct: "distinct (lck_keys M data)"
 unfolding lck_keys_def lck_trace_keys_def lck_composition_keys_def
 by (auto simp: distinct_map inj_on_def)

lemma lck_only_fri:
 "key\<in>set(lck_keys M data) \<Longrightarrow>
   (\<exists>i v. key=TraceFriChallenge i v \<or> key=CompositionFriChallenge i v)"
 unfolding lck_keys_def lck_trace_keys_def lck_composition_keys_def by auto

lemma lck_not_query:
 "QueryIndexChallenge j v\<notin>set(lck_keys M data)"
 using lck_only_fri by fastforce

lemma lck_prefix_exists:
 assumes header: "as_header M start data"
   and split: "weighted_semantic_header data=xs@ys"
 shows "\<exists>v. ro_absorb_lookup_chain (channel_for_hash_map M)
   (PState adversary_initial_state) xs v"
proof -
 obtain rest where chain: "ro_absorb_lookup_chain (channel_for_hash_map M)
   (PState adversary_initial_state) (weighted_semantic_header data@rest) start"
   using header unfolding as_header_def by blast
 have "ro_absorb_lookup_chain (channel_for_hash_map M)
   (PState adversary_initial_state) (xs@(ys@rest)) start"
   using chain by (simp only: split append_assoc)
 then show ?thesis using ro_absorb_lookup_chain_append_split[where xs=xs]
   by blast
qed

lemma lck_trace_prefix_exists:
 assumes header: "as_header M start data"
 shows "\<exists>v. ro_absorb_lookup_chain (channel_for_hash_map M)
   (PState adversary_initial_state)
   (staged_trace_root data#take (Suc i) (staged_trace_fri_roots data)) v"
proof -
 let ?ys="drop (Suc i) (staged_trace_fri_roots data)@[staged_trace_final data]@
   staged_alphas data@[staged_degree data]@staged_composition_fri_roots data@[staged_composition_final data]"
 show ?thesis
  by (rule lck_prefix_exists[OF header, where ys="?ys"])
    (simp add: weighted_semantic_header_def verifier_header_messages_def append_assoc[symmetric])
qed

lemma lck_composition_prefix_exists:
 assumes header: "as_header M start data"
 shows "\<exists>v. ro_absorb_lookup_chain (channel_for_hash_map M)
   (PState adversary_initial_state)
   (composition_fri_challenge_prefix_messages (staged_trace_root data)
     (staged_trace_fri_roots data) (staged_trace_final data) (staged_alphas data)
     (staged_degree data) (staged_composition_fri_roots data) i) v"
proof -
 let ?ys="drop (Suc i) (staged_composition_fri_roots data)@[staged_composition_final data]"
 show ?thesis
  by (rule lck_prefix_exists[OF header, where ys="?ys"])
    (simp add: weighted_semantic_header_def verifier_header_messages_def
      composition_fri_challenge_prefix_messages_def)
qed

lemma lck_endpoint_extension:
 assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
   and exists: "\<exists>v. ro_absorb_lookup_chain (channel_for_hash_map M)
     (PState adversary_initial_state) xs v"
 shows "lck_endpoint U xs=lck_endpoint M xs"
proof -
 obtain v where chain: "ro_absorb_lookup_chain (channel_for_hash_map M)
   (PState adversary_initial_state) xs v" using exists by blast
 have final: "ro_absorb_lookup_chain (channel_for_hash_map U)
   (PState adversary_initial_state) xs v"
   by (rule ro_absorb_lookup_chain_mono[OF chain ext])
 show ?thesis using lck_endpoint_eq[OF chain] lck_endpoint_eq[OF final] by simp
qed

lemma lck_keys_extension:
 assumes ext: "channel_for_hash_map M\<le>channel_for_hash_map U"
   and header: "as_header M start data"
 shows "lck_keys U data=lck_keys M data"
proof -
 have trace: "\<And>i. lck_endpoint U (staged_trace_root data#take (Suc i) (staged_trace_fri_roots data))=
   lck_endpoint M (staged_trace_root data#take (Suc i) (staged_trace_fri_roots data))"
   by (rule lck_endpoint_extension[OF ext lck_trace_prefix_exists[OF header]])
 have comp: "\<And>i. lck_endpoint U (composition_fri_challenge_prefix_messages
   (staged_trace_root data) (staged_trace_fri_roots data) (staged_trace_final data)
   (staged_alphas data) (staged_degree data) (staged_composition_fri_roots data) i)=
   lck_endpoint M (composition_fri_challenge_prefix_messages
   (staged_trace_root data) (staged_trace_fri_roots data) (staged_trace_final data)
   (staged_alphas data) (staged_degree data) (staged_composition_fri_roots data) i)"
   by (rule lck_endpoint_extension[OF ext lck_composition_prefix_exists[OF header]])
 show ?thesis unfolding lck_keys_def lck_trace_keys_def lck_composition_keys_def
   by (simp only: trace comp)
qed

end

subsection \<open>Latent Challenge Score\<close>

context soundness
begin

definition lcs_score where
 "lcs_score ks S p rt ffs cfs n i v M =
   lca_avg ks (fmlookup M) (\<lambda>bs. lpd_score (S bs) p rt ffs cfs n i v M)"

lemma lcs_lookup_update:
 "fmlookup (fmupd k z M)=(fmlookup M)(k:=Some z)"
 by (rule ext) simp

lemma lcs_fri_route_update:
 assumes fri: "(\<exists>j w. key=TraceFriChallenge j w \<or> key=CompositionFriChallenge j w)"
 shows "lpa_route rt ffs cfs (fmupd key z M)=lpa_route rt ffs cfs M"
proof -
 have fibers: "\<And>v w. pair_route_fiber UNIV rt ffs cfs v
     (channel_for_hash_map (fmupd key z M)) w=
   pair_route_fiber UNIV rt ffs cfs v (channel_for_hash_map M) w"
    using fri
    by (elim exE disjE; simp add: pair_route_fiber_def serial_round_authenticated_def
      partial_authenticated_table_def fri_mfold_chunks_authenticated_def
      fri_layer_chunk_authenticated_def)
  show ?thesis unfolding lpa_route_def Let_def
    by (simp only: fibers)
qed

lemma lcs_fri_score_update:
 assumes fri: "(\<exists>j w. key=TraceFriChallenge j w \<or> key=CompositionFriChallenge j w)"
 shows "lpd_score S p rt ffs cfs n i v (fmupd key z M)=
   lpd_score S p rt ffs cfs n i v M"
proof -
 have samples: "lpa_samples (fmupd key z M)=lpa_samples M"
   using fri by (auto simp: lpa_samples_def fun_eq_iff)
 show ?thesis unfolding lpd_score_def lcs_fri_route_update[OF fri] samples ..
qed

lemma lcs_fri_fresh_average:
 assumes distinct: "distinct ks" and fresh: "fmlookup M key=None"
   and fri: "\<exists>j w. key=TraceFriChallenge j w \<or> key=CompositionFriChallenge j w"
 shows "lpw_mean (\<lambda>z. lcs_score ks S p rt ffs cfs n i v (fmupd key z M))=
   lcs_score ks S p rt ffs cfs n i v M"
 unfolding lcs_score_def lcs_fri_score_update[OF fri] lcs_lookup_update
 by (rule lca_avg_fresh_update) (rule distinct, rule fresh)

lemma lcs_query_fresh_average:
 assumes fresh: "fmlookup M (QueryIndexChallenge j w)=None"
   and outside: "QueryIndexChallenge j w\<notin>set ks"
 shows "lpw_mean (\<lambda>z. lcs_score ks S p rt ffs cfs n i v
    (fmupd (QueryIndexChallenge j w) z M))=
   lcs_score ks S p rt ffs cfs n i v M"
 unfolding lcs_score_def lcs_lookup_update lca_avg_update_irrelevant[OF outside]
 by (simp only: lca_avg_swap lpd_query_fresh_average[OF fresh])

lemma lcs_cached:
 assumes cached: "fmlookup M key=Some z"
 shows "lcs_score ks S p rt ffs cfs n i v (fmupd key z M)=
   lcs_score ks S p rt ffs cfs n i v M"
proof -
 have "fmupd key z M=M"
   by (rule Finite_Map.fmap_ext) (use cached in auto)
 then show ?thesis by simp
qed

lemma lcs_other_update:
 assumes mass: "\<And>bs. lpw_mass (S bs)\<le>p"
   and outside: "key\<notin>set ks"
   and fresh: "fmlookup M key=None"
   and nonquery: "\<And>j w. key\<noteq>QueryIndexChallenge j w"
   and nohit: "z\<notin>weighted_semantic_interval_targets M"
   and roots: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets M"
   and clean: "\<not>hash_map_output_collision (channel_for_hash_map (fmupd key z M))"
 shows "lcs_score ks S p rt ffs cfs n i v (fmupd key z M)\<le>
   lcs_score ks S p rt ffs cfs n i v M"
 unfolding lcs_score_def lcs_lookup_update lca_avg_update_irrelevant[OF outside]
 by (rule lca_avg_mono)
    (unfold lpd_score_def, rule lpa_nonquery_score[OF mass fresh nonquery nohit roots clean])

lemma lcs_virgin_region:
 assumes mass: "\<And>bs. lpw_mass (S bs)\<le>p"
   and empty: "\<And>j w. w\<in>V \<Longrightarrow> lpa_samples M (j,w)=None"
   and closed: "\<And>(j::nat) u x w. u\<in>V \<Longrightarrow> lpa_route rt ffs cfs M (j,u) x=Some w \<Longrightarrow> w\<in>V"
   and vertex: "v\<in>V"
 shows "lcs_score ks S p rt ffs cfs n i v M\<le>p^n"
proof -
 have point: "\<And>bs. lpd_score (S bs) p rt ffs cfs n i v M\<le>p^n"
   unfolding lpd_score_def
   apply (rule lpw_score_virgin_region[where V=V])
    apply (rule mass)
    apply (erule empty)
    apply (erule (1) closed)
    by (rule vertex)
  have "lca_avg ks (fmlookup M) (\<lambda>bs. lpd_score (S bs) p rt ffs cfs n i v M)
   \<le>lca_avg ks (fmlookup M) (\<lambda>bs. p^n)"
   by (rule lca_avg_mono) (rule point)
 then show ?thesis by (simp only: lcs_score_def lca_avg_const)
qed

end

subsection \<open>Latent Challenge Oracle Drift\<close>

context soundness
begin

lemma lcd_fresh_probe_bound:
 assumes fresh: "fmlookup (HashMap s) key=None"
   and average: "lpw_mean (\<lambda>z. F(fmupd key z (HashMap s)))\<le>F(HashMap s)"
 shows "wp (pair_probe key)
   (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
     if guard e t then F(HashMap t) else 0) s\<le>F(HashMap s)"
proof -
 have "wp (pair_probe key)
   (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
     if guard e t then F(HashMap t) else 0) s \<le>
   wp (pair_probe key) (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
     F(fmupd key (ep_raw e) (HashMap s))) s"
 proof (rule wp_mono_on_support)
  fix out assume mem: "out\<in>set_dist (execute (pair_probe key) s)"
  show "(case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> if guard e t then F(HashMap t) else 0)\<le>
    (case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow> F(fmupd key (ep_raw e) (HashMap s)))"
  proof (cases out)
   case None then show ?thesis by simp
  next
   case (Some et)
   obtain e t where et: "et=(e,t)" by (cases et) simp
   obtain raw where e: "e=(HashMap s,key,raw)" and maps: "HashMap t=fmupd key raw (HashMap s)"
     using mem Some et by (auto elim: lpd_probe_state)
   show ?thesis by (simp add: Some et e maps ep_raw_def split: if_splits)
  qed
 qed
 also have "...=lpw_mean (\<lambda>z. F(fmupd key z (HashMap s)))"
   by (rule lpd_probe_mean[OF fresh])
 also have "...\<le>F(HashMap s)" by (rule average)
 finally show ?thesis .
qed

lemma lcd_stopped_probe:
 assumes distinct: "distinct ks"
   and tags: "\<And>k. k\<in>set ks \<Longrightarrow> \<exists>j w. k=TraceFriChallenge j w \<or> k=CompositionFriChallenge j w"
   and mass: "\<And>bs. lpw_mass (S bs)\<le>p"
   and roots: "causal_route_roots rt ffs cfs\<subseteq>weighted_semantic_interval_targets (HashMap s)"
 shows "wp (pair_probe key)
   (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
     if \<not>fc_bad_record {} e \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
     then lcs_score ks S p rt ffs cfs n i v (HashMap t) else 0) s
   \<le>lcs_score ks S p rt ffs cfs n i v (HashMap s)"
proof -
 let ?G="\<lambda>e t. \<not>fc_bad_record {} e \<and>
   \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))"
 let ?F="lcs_score ks S p rt ffs cfs n i v"
 show ?thesis
 proof (cases "fmlookup (HashMap s) key=None \<and> (key\<in>set ks \<or> (\<exists>j w. key=QueryIndexChallenge j w))")
  case True
  have fresh: "fmlookup (HashMap s) key=None" using True by blast
  have average: "lpw_mean (\<lambda>z. ?F(fmupd key z (HashMap s)))=?F(HashMap s)"
  proof (cases "key\<in>set ks")
   case True
   show ?thesis by (rule lcs_fri_fresh_average[OF distinct fresh tags[OF True]])
  next
   case False
   obtain j w where key: "key=QueryIndexChallenge j w" using True False by blast
   show ?thesis unfolding key
    by (rule lcs_query_fresh_average[OF fresh[unfolded key] False[unfolded key]])
  qed
  show ?thesis by (rule lcd_fresh_probe_bound[OF fresh]) (simp only: average)
 next
  case unresolved: False
  show ?thesis
  proof (rule wp_le_const_on_support)
   fix out assume mem: "out\<in>set_dist (execute (pair_probe key) s)"
   show "(case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
     if ?G e t then ?F(HashMap t) else 0)\<le>?F(HashMap s)"
   proof (cases out)
    case None then show ?thesis by simp
   next
    case (Some et)
    obtain e t where et: "et=(e,t)" by (cases et) simp
    obtain raw where e: "e=(HashMap s,key,raw)" and maps: "HashMap t=fmupd key raw (HashMap s)"
      and lookup: "fmlookup (HashMap s) key=None \<or> fmlookup (HashMap s) key=Some raw"
      using mem Some et by (auto elim: lpd_probe_state)
    show ?thesis
    proof (cases "?G e t")
     case False then show ?thesis
       by (auto simp: Some et)    next
     case good: True
     have bound: "?F(HashMap t)\<le>?F(HashMap s)"
     proof (cases "fmlookup (HashMap s) key=None")
      case True
      have outside: "key\<notin>set ks" and nonquery: "\<And>j w. key\<noteq>QueryIndexChallenge j w"
        using unresolved True by blast+
      have nohit: "raw\<notin>weighted_semantic_interval_targets (HashMap s)"
        using good True by (simp add: e fc_bad_record_def fc_target_def)
      have clean: "\<not>hash_map_output_collision (channel_for_hash_map (fmupd key raw (HashMap s)))"
        using good maps by simp
      show ?thesis unfolding maps
        by (rule lcs_other_update[OF mass outside True nonquery nohit roots clean])
     next
      case False
      have cached: "fmlookup (HashMap s) key=Some raw" using lookup False by blast
      show ?thesis by (simp only: maps lcs_cached[OF cached])
     qed
     show ?thesis using bound good by (simp add: Some et)
    qed
   qed
  qed
 qed
qed

end

subsection \<open>Latent Challenge FRI Family\<close>

context soundness
begin

definition lcf_data where
 "lcf_data data bs = data\<lparr>
   staged_trace_fri_challenges := take (length(staged_trace_fri_roots data)) bs,
   staged_composition_fri_challenges := drop (length(staged_trace_fri_roots data)) bs\<rparr>"

definition lcf_raw where
 "lcf_raw N r is_trace prefix prefix_state M data bs =
   query_index_raw_preimage (fri_mca_residual_query_indices N r is_trace
     prefix prefix_state (lcf_data data bs) (channel_for_hash_map M))"

definition ro_mca_weighted_fri_base where
 "ro_mca_weighted_fri_base r is_trace = nnreal (query_raw_preimage_card_envelope
   (fri_mca_residual_branch_bound r is_trace))/nnreal size"

lemma lcf_mass:
 "lpw_mass(lcf_raw N r is_trace prefix prefix_state M data bs)\<le>ro_mca_weighted_fri_base r is_trace"
 unfolding lcf_raw_def ro_mca_weighted_fri_base_def by (rule cfa_branch_mass)

lemma lcf_data_actual:
 assumes len: "length (staged_trace_fri_challenges data)=length(staged_trace_fri_roots data)"
 shows "lcf_data data (staged_trace_fri_challenges data@staged_composition_fri_challenges data)=data"
 using len unfolding lcf_data_def by simp

lemma lcf_stopped_probe:
 fixes N r is_trace prefix prefix_state M
 assumes header: "as_header (HashMap s) start data"
 defines "ks \<equiv> lck_keys (HashMap s) data"
   and "S \<equiv> lcf_raw N r is_trace prefix prefix_state M data"
   and "p \<equiv> ro_mca_weighted_fri_base r is_trace"
   and "rt \<equiv> staged_trace_root data"
   and "ffs \<equiv> map (\<lambda>root. ((0::'f),root)) (staged_trace_fri_roots data)"
   and "cfs \<equiv> map (\<lambda>root. ((0::'f),root)) (staged_composition_fri_roots data)"
 shows "wp (pair_probe key)
    (\<lambda>out. case out of None \<Rightarrow> 0 | Some(e,t) \<Rightarrow>
      if \<not>fc_bad_record {} e \<and> \<not>hash_map_output_collision (channel_for_hash_map (HashMap t))
      then lcs_score ks S p rt ffs cfs n i v (HashMap t) else 0) s
    \<le>lcs_score ks S p rt ffs cfs n i v (HashMap s)"
 unfolding ks_def S_def p_def rt_def ffs_def cfs_def
 by (rule lcd_stopped_probe; (rule lck_distinct | rule lck_only_fri |
      rule lcf_mass | rule as_header_roots_targets[OF header]); assumption?)

lemma lcf_virgin_cap:
 assumes empty: "\<And>j w. w\<in>V \<Longrightarrow> fmlookup U (QueryIndexChallenge j w)=None"
   and closed: "\<And>(j::nat) w x y. w\<in>V \<Longrightarrow> lpa_route rt ffs cfs U (j,w) x=Some y \<Longrightarrow> y\<in>V"
   and vertex: "v\<in>V"
 shows "lcs_score ks (lcf_raw N r is_trace prefix prefix_state M data)
   (ro_mca_weighted_fri_base r is_trace) rt ffs cfs n i v U \<le> (ro_mca_weighted_fri_base r is_trace)^n"
 apply (rule lcs_virgin_region[where V=V])
 by (auto simp: lpa_samples_def intro: lcf_mass empty closed vertex)

end

end
