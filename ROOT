session Stark_Core in "Core" = Berlekamp_Zassenhaus +
  options [document = false]
theories [document = true]
    Stark

session Stark_Completeness in "Completeness" = Stark_Core +
  options [document = false]
theories [document = true]
    Completeness

session Stark_Examples in "Examples" = Stark_Core +
  options [document = false]
theories [document = true]
    Square_Sequence

session Stark in "Soundness" = Stark_Core +
  options [document = pdf, document_output = "../output"]
  sessions
    Stark_Completeness
    Stark_Examples
  theories
    Soundness_FRI_Trace_Restricted_Query_Endpoint
    Stark_Document
  document_theories
    Stark_Core.NNReal
    Stark_Core.Prob_Dist
    Stark_Core.Hash_Monad
    Stark_Core.Channel_Core
    Stark_Core.Channel_Transcript
    Stark_Core.Channel_Instances
    Stark_Core.Channel
    Stark_Core.Galois_Field_5
    Stark_Core.Merkle_Tree
    Stark_Core.Prob_Monad
    Stark_Core.Stark
    Stark_Completeness.Completeness_Core
    Stark_Completeness.Completeness_Algebra
    Stark_Completeness.Completeness_Transcript
    Stark_Completeness.Completeness_Replay
    Stark_Completeness.Completeness_Query
    Stark_Completeness.Completeness_FRI
    Stark_Completeness.Completeness_Verifier
    Stark_Completeness.Completeness
    Stark_Examples.Square_Sequence
  document_files
    "root.tex"
