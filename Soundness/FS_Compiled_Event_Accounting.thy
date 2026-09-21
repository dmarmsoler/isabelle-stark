(* Title: Stark/FS_Compiled_Event_Accounting.thy
   License: BSD-3-Clause *)

theory FS_Compiled_Event_Accounting
  imports "FS_Probability_Accounting"
    "Soundness_FRI_Weighted_Residual_Union"
begin

section \<open>Final-map event transport for the replay compiler\<close>

text \<open>Only final-map observations are transported here. Saved-prefix bad events
  are not claimed to be final-map observations. Witness erasure and the compiler
  equality preserve arbitrary oracle-dependent producer outputs.\<close>

context soundness
begin

definition fs_map_event where
  "fs_map_event E out \<longleftrightarrow>
    (case out of None \<Rightarrow> False | Some(x,s) \<Rightarrow> E (HashMap s))"

lemma fs_map_event_path_map:
  fixes m :: "('a, 'f protocol_channel) state_monad"
  shows "wp_event (m \<bind> (\<lambda>x. return (f x))) (fs_map_event E) s =
    wp_event m (fs_map_event E) s"
  unfolding wp_event_def wp_bind_return_map fs_map_event_def
  by (rule arg_cong[where f="\<lambda>P. wp m P s"], rule ext)
    (auto split: option.splits prod.splits)

lemma fs_map_event_compile:
  assumes "fs_fixed P" "fs_query_bound Q P"
  shows "wp_event (ro_absorb_checked_staged_security_experiment (fs_compile_replay A P))
      (fs_map_event E) adversary_initial_state =
    wp_event (fs_security_experiment P) (fs_map_event E) adversary_initial_state"
  using fs_compile_replay_wp[OF assms, where A=A and base=adversary_initial_state
    and F="\<lambda>out. if fs_map_event E out then 1 else 0"]
  by (simp add: fs_ignores_transcript_def fs_map_event_def wp_event_def
    verifier_state_from_adversary_def adversary_initial_state_def)

lemma fs_map_event_witness_erase:
  "wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      (fs_map_event E) s =
    wp_event (ro_absorb_checked_staged_security_experiment A) (fs_map_event E) s"
proof -
  have first: "wp_event (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (fs_map_event E) s =
    wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      (fs_map_event E) s"
    using fs_map_event_path_map[where
      m="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A"
      and f="\<lambda>(((prefix_with_state,data,query_start,raws,query_states),attacker_state),result).
        (((data,query_start,raws,query_states),attacker_state),result)" and E=E and s=s]
    by (simp only: split_def
      ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection_all_rounds[unfolded split_def])
  have queries: "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
      (fs_map_event E) s =
    wp_event (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
      (fs_map_event E) s"
    using fs_map_event_path_map[where
      m="ro_absorb_checked_staged_security_experiment_with_query_witnesses A"
      and f="\<lambda>(((data,query_start,raws,query_states),attacker_state),result).
        ((data,attacker_state),result)" and E=E and s=s]
    by (simp only: split_def
      ro_absorb_checked_staged_security_experiment_with_query_witnesses_projection[unfolded split_def])
  have data: "wp_event (ro_absorb_checked_staged_security_experiment A) (fs_map_event E) s =
    wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A) (fs_map_event E) s"
    using fs_map_event_path_map[where
      m="ro_absorb_checked_staged_security_experiment_with_data_state A"
      and f=snd and E=E and s=s]
    by (simp only: ro_absorb_checked_staged_security_experiment_with_data_state_projection)
  show ?thesis using first queries data by simp
qed

lemma fs_final_collision_as_map:
  "final_hash_collision_event out =
    fs_map_event (\<lambda>M. hash_map_output_collision (channel_for_hash_map M)) out"
  by (auto simp: fs_map_event_def final_hash_collision_event_def
    hash_map_output_collision_def channel_for_hash_map_def
    split: option.splits prod.splits)

lemma fs_initial_target_as_map:
  "hash_new_output_hit_event B adversary_initial_state out =
    fs_map_event (\<lambda>M. hash_map_new_output_hit B adversary_initial_state
      (channel_for_hash_map M)) out"
  by (auto simp: fs_map_event_def hash_new_output_hit_event_def
    hash_map_new_output_hit_def hash_map_output_values_def channel_for_hash_map_def
    split: option.splits prod.splits)

lemma fs_direct_final_collision:
  assumes "fs_query_bound Q P"
  shows "wp_event (fs_security_experiment P) final_hash_collision_event adversary_initial_state \<le>
    hash_collision_budget_value 0 (fs_direct_hash_budget Q)"
proof -
  have event: "hash_new_collision_event adversary_initial_state = final_hash_collision_event"
    by (rule ext)
      (auto simp: hash_new_collision_event_def final_hash_collision_event_def
        hash_map_new_output_collision_def
        split: option.splits prod.splits)
  show ?thesis using fs_direct_new_collision[OF assms] by (simp only: event)
qed

lemma fs_compiled_final_collision:
  assumes "fs_fixed P" "fs_query_bound Q P"
  shows "wp_event
    (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      (fs_compile_replay A P)) final_hash_collision_event adversary_initial_state \<le>
    hash_collision_budget_value 0 (fs_direct_hash_budget Q)"
proof -
  have transport: "wp_event
    (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      (fs_compile_replay A P)) final_hash_collision_event adversary_initial_state =
    wp_event (fs_security_experiment P) final_hash_collision_event adversary_initial_state"
    by (simp add: fs_final_collision_as_map[abs_def] fs_map_event_witness_erase
      fs_map_event_compile[OF assms])
  show ?thesis unfolding transport by (rule fs_direct_final_collision[OF assms(2)])
qed

lemma fs_compiled_initial_target:
  assumes "fs_fixed P" "fs_query_bound Q P"
  shows "wp_event
    (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      (fs_compile_replay A P))
    (hash_new_output_hit_event B adversary_initial_state) adversary_initial_state \<le>
    hash_target_budget_value B (fs_direct_hash_budget Q)"
proof -
  have transport: "wp_event
    (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      (fs_compile_replay A P))
    (hash_new_output_hit_event B adversary_initial_state) adversary_initial_state =
    wp_event (fs_security_experiment P)
      (hash_new_output_hit_event B adversary_initial_state) adversary_initial_state"
    by (simp add: fs_initial_target_as_map[abs_def] fs_map_event_witness_erase
      fs_map_event_compile[OF assms])
  show ?thesis unfolding transport by (rule fs_direct_fixed_target[OF assms(2)])
qed

end
end


