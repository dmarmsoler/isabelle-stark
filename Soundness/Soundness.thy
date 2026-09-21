(*  Title:      Stark/Soundness.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness
  imports
    Soundness_Staged_Aligned_Current_Query_Path
    Soundness_Staged_Aligned_Current_Empty
    Soundness_Alpha_Fixed_Candidate
    Staged_Security_Experiment_Composition_Query_Header_Rounds
    Staged_Security_Experiment_Composition_Query_Canonical
    Staged_Security_Experiment_Composition_Query_Current

begin

text \<open>
  Aggregator for the soundness infrastructure used by both the legacy and
  conditioned public routes.  The downstream conditioned endpoint is exported
  by \<^file>\<open>Soundness_FRI_Conditioned_Explicit_All_Rounds_Bound.thy\<close>:
  its theorem has the original three premises and an adversary-independent
  arithmetic error.  Its symbolic feasibility corollary proves acceptance
  probability strictly below one under explicit field-size, round,
  sampler-envelope, degree, and staged-budget inequalities.  No concrete
  cryptographic parameter instance is claimed.  The separate downstream
  coarse-compatibility layer preserves the former coarse bound for the same
  acceptance experiment.  These downstream theories deliberately do not
  become imports here, because older soundness layers import this aggregator.
\<close>

end
