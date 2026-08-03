(*  Title:      Stark/Channel.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Channel
  imports Channel_Instances
begin

text \<open>
  Compatibility umbrella for the channel development.  The imported theories
  define the protocol state, transcript operations, Fiat-Shamir oracle calls,
  and concrete field instances used by the STARK prover and verifier.
\<close>

end
