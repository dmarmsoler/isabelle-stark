(*  Title:      Stark/Soundness_Staged_Partial_Merkle.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Partial_Merkle
  imports Soundness_Staged_Bounds
begin

text \<open>
  Aggregator for staged partial-Merkle soundness infrastructure.  The old
  public-path compatibility wrappers based on partial-Merkle event-bound
  premises were removed before publication; downstream active-route theories
  import this file only for the underlying staged bounds.
\<close>

end
