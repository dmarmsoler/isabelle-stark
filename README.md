# Isabelle/STARK: A Formalization of zk-STARK in Isabelle/HOL

This repository contains an Isabelle/HOL formalization of a STARK-style transparent proof protocol, including an executable prover/verifier model, an honest-completeness theorem, a staged soundness theorem, and a small square-sequence example.

## Overview

The development formalizes a representative STARK protocol in Isabelle/HOL. It includes a finite probabilistic state monad, channel and transcript operations, a Merkle-tree model, prover and verifier monads, algebraic domain assumptions, completeness proofs, and staged soundness proofs. The protocol is modeled as executable Isabelle definitions rather than as informal pseudocode. The square-sequence example provides a small concrete instance over GF(5). This is a mechanized research formalization, not production cryptographic software.

## Main Results

- Core protocol model: `Core/Stark.thy`, locales `stark`, `prover`, and `verifier`.
- Honest completeness: `Completeness/Completeness_Verifier.thy`, theorem `completeness`.
- Public staged soundness: `Soundness/Soundness_FRI_Trace_Restricted_Query_Endpoint.thy`, theorem `stark_soundness`.
- Executable example: `Examples/Square_Sequence.thy`.

## Repository Layout

| Path            | Contents                                                                                                                           |
| --------------- | ---------------------------------------------------------------------------------------------------------------------------------- |
| `Core/`         | Probabilistic monad, channel model, transcript operations, Merkle tree, finite-field example, and core STARK protocol definitions. |
| `Completeness/` | Honest-completeness proof for the prover/verifier execution.                                                                       |
| `Soundness/`    | Staged adversary experiment, bad-event reductions, FRI/query/Merkle bounds, and final soundness theorem.                           |
| `Examples/`     | Small executable square-sequence instance over GF(5).                                                                              |
| `ROOT`          | Isabelle session definitions.                                                                                                      |

## Requirements

- Isabelle2025-2.
- A matching Archive of Formal Proofs version installed as an Isabelle component.
- Optional, for building the technical report: `latexmk`, `pdflatex`, and `bibtex`.

The local development environment used AFP `VERSION=2025-1`.
For a public checkout, it is enough that the matching AFP release is available
as an Isabelle component.

## Building

Run the trusted build for all repository sessions with:

```sh
isabelle build -D .
```

Individual sessions can also be built separately:

```sh
isabelle build Stark_Core
isabelle build Stark_Completeness
isabelle build Stark_Examples
isabelle build Stark
```

## Reading Guide

A useful reading order is:

1. `Core/Prob_Monad.thy`
2. `Core/Channel.thy`
3. `Core/Merkle_Tree.thy`
4. `Core/Stark.thy`
5. `Completeness/Completeness.thy`
6. `Soundness/Security_Experiment.thy`
7. `Soundness/Soundness_FRI_Trace_Restricted_Query_Endpoint.thy`
8. `Examples/Square_Sequence.thy`

## Scope And Limitations

This repository formalizes a representative STARK-style protocol for research and proof-engineering purposes. The square-sequence example is intentionally small and executable; it is not a security-scale instance. The final soundness bound is explicit but conservative. The formalization is not an implementation intended for deployment.

## License

This repository is distributed under the BSD-3-Clause license. See `LICENSE`.
