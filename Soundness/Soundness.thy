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
  Aggregator for the soundness infrastructure used by the active public
  endpoint.  The public soundness theorem is exported by
  \<^file>\<open>Soundness_FRI_Trace_Restricted_Query_Endpoint.thy\<close>.
\<close>

end
