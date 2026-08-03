(*  Title:      Stark/Completeness.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Completeness
  imports Completeness_Verifier
begin

text \<open>
  Public entry point for the honest-completeness development.  The imported
  theories reduce the probabilistic verifier failure event to deterministic
  algebraic, transcript, Merkle, query, and FRI facts for the honest prover.
\<close>

end
