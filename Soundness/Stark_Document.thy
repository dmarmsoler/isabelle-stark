(*  Title:      Stark/Stark_Document.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Stark_Document
  imports
    Soundness_FRI_Trace_Restricted_Query_Endpoint
    Stark_Completeness.Completeness
    Stark_Examples.Square_Sequence
begin

text \<open>
  Document aggregation theory for the generated Isabelle proof document.  The
  main proof entry points remain the completeness theorem, the executable
  example, and the public soundness endpoint imported above.
\<close>

end
