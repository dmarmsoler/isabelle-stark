# Isabelle/STARK: Mechanized Soundness for a STARK-Style Protocol

This repository formalizes a STARK-style protocol in Isabelle/HOL, connecting
an executable probabilistic verifier to honest completeness and query-bounded
soundness for adaptive Fiat–Shamir transcript producers.

The certified square-sequence instance bounds false-endpoint acceptance by
`2^-137` for every modeled FS program satisfying `fs_query_bound (2^20) P`,
using a certified 192-bit field, trace length 1024 and 640 query repetitions.
Correct endpoints have honest acceptance probability one in the same final
verifier. These are fixed-statement, classical field-valued ROM results.
The development does not prove zero knowledge, knowledge extraction, QROM
security, correspondence to a deployed bit-hash implementation, or an
unrestricted 137-bit work factor.

Start with [Current results and theorem map](PUBLICATION.md) and
[Reproduction and trust-manifest checks](REPRODUCING.md).

This snapshot prepares a forthcoming minimal release for
[dmarmsoler/isabelle-stark](https://github.com/dmarmsoler/isabelle-stark).
As checked on 21 September 2026, that public repository provides an earlier
version; public availability of the release described here and its historical
sources remains pending.

## Main results and retained example

[PUBLICATION.md](PUBLICATION.md#claim-to-theorem-map) maps the ten selected
publication results to their exact theorem names. The build-checked
[Publication_Manifest](Soundness/Publication_Manifest.thy) exports their
statements, explicit premises and trust information. The results cover square
workload semantics, honest RO acceptance, the shared verifier, adaptive and
private-randomness FS transport, replay allowance, generic first-root
soundness, the ledger comparison and the concrete `2^-137` certificate.

The small executable [Square Sequence example](Examples/Square_Sequence.thy)
over GF(5) is also retained. It is checked in `Stark_Examples` and appears in
the generated proof document. The certified 192-bit instance is a separate
mathematical example: its generator is chosen from proved existence rather
than supplied as an extracted executable numeral.

The release contains 487 theories: exactly the transitive repository theory
imports of `Publication_Manifest` and `Square_Sequence`, including those two
entry points. All Core, Completeness and Examples theories remain.
The cleanup removes 84 Soundness theories outside this closure and does not
change any retained proof source or theorem statement. Historical-looking
theories still imported by the selected results remain necessary for this
unmodified proof route.

## Repository layout

| Path                           | Contents                                                                               |
| ------------------------------ | -------------------------------------------------------------------------------------- |
| [Core/](Core/)                 | Probability, channels, Merkle trees, the finite-field example and protocol definitions |
| [Completeness/](Completeness/) | Honest completeness of the core prover/verifier execution                              |
| [Examples/](Examples/)         | Executable GF(5) example, prime-field certification and scalable square workload       |
| [Soundness/](Soundness/)       | Soundness, FS transport/accounting and concrete honest RO completeness                 |
| [ROOT](ROOT)                   | The four Isabelle sessions and proof-document configuration                            |

## Requirements

- Isabelle2025-2.
- AFP snapshot `afp-2026-08-07` for Isabelle2025-2, installed as a component.
- The TeX toolchain required by Isabelle's configured PDF output.
- Optional, for the separate technical report: `latexmk`, `pdflatex` and `bibtex`.

Pinned downloads, checksums, installation instructions and the scope of prior
reproduction runs are documented in [REPRODUCING.md](REPRODUCING.md).

## Building and checking

Run the normal build for all four sessions, including the executable example:

```sh
isabelle build -D .
```

To build and also export the checked ten-theorem publication manifest:

```sh
bash tools/check-publication.sh /path/to/Isabelle2025-2/bin/isabelle
```

The checker runs one normal build, records source hashes and exports the
manifest without starting another build. The generated proof document is
[output/document.pdf](output/document.pdf).

Individual sessions can be built separately:

```sh
isabelle build -d . Stark_Core
isabelle build -d . Stark_Completeness
isabelle build -d . Stark_Examples
isabelle build -d . Stark
```

The separate technical report can be built with `make -C report`.

## Reading guide

1. [PUBLICATION.md](PUBLICATION.md): claims, assumptions, theorem map and limits.
2. [Core/Stark.thy](Core/Stark.thy): protocol definitions and locales.
3. [Examples/Square_Sequence.thy](Examples/Square_Sequence.thy): executable small-field instance.
4. [FS_Adversary_Model](Soundness/FS_Adversary_Model.thy),
   [FS_Adaptive_Staged_Embedding](Soundness/FS_Adaptive_Staged_Embedding.thy) and
   [FS_Replay_Allowance](Soundness/FS_Replay_Allowance.thy): attacker language,
   acceptance transport and operational allowance.
5. [FS_First_Root_Soundness](Soundness/FS_First_Root_Soundness.thy) and
   [FS_Square_192_137](Soundness/FS_Square_192_137.thy): generic and concrete soundness.
6. [Square_Sequence_192_RO_Completeness](Soundness/Square_Sequence_192_RO_Completeness.thy):
   honest acceptance by the absorbing RO verifier.
7. [REPRODUCING.md](REPRODUCING.md): build, manifest checks and remaining release gates.

## Related work and contribution

This project connects ideas from several lines of research:

- [Interactive Oracle Proofs](https://eprint.iacr.org/2016/116),
  [FRI](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.14)
  and the [original STARK paper](https://eprint.iacr.org/2018/046) provide the
  foundations: checking selected parts of a proof, testing whether data is
  close to a low-degree polynomial, and proving computations transparently.
- Garreta, Mohnblatt and Wagner's
  [simplified FRI soundness proof](https://eprint.iacr.org/2025/1993) and the
  [simple-rbr-fri Lean project](https://github.com/zksecurity/simple-rbr-fri)
  are closely related to the mutual correlated agreement (MCA) reasoning
  used here. The Lean project formalizes FRI soundness and completeness.
- [WHIR](https://eprint.iacr.org/2024/1586) develops related polynomial
  proximity tests with fast verification and supplies supporting mathematics
  referenced by the simplified FRI formalization.
- [Block et al.](https://eprint.iacr.org/2023/1071) analyze the security of
  FRI and related protocols after applying Fiat–Shamir.
  [Block and Tiwari](https://eprint.iacr.org/2024/1161) examine how concrete
  parameter choices affect provable and conjectured security.
- [ArkLib](https://github.com/Verified-zkEVM/ArkLib) develops reusable Lean
  infrastructure for assembling and verifying proof systems, with work on
  FRI, Merkle commitments and Fiat–Shamir.
- [Bailey and Miller](https://eprint.iacr.org/2023/656) mechanize soundness
  proofs for six pairing-based SNARKs, including Groth16, in Lean.
- The [Cairo encoding](https://arxiv.org/abs/2109.14534) and
  [S-two AIR](https://arxiv.org/abs/2606.04311) verification projects prove
  that algebraic constraints correctly describe Cairo program execution.
- [VCVio](https://eprint.iacr.org/2024/1819) provides Lean proofs about
  oracle computations and Fiat–Shamir for sigma protocols.
  [CryptHOL](https://eprint.iacr.org/2017/753) provides Isabelle infrastructure
  for probabilistic games and cryptographic security proofs.

Isabelle/STARK's distinctive contribution is a machine-checked connection
between the meaning of a computation, honest acceptance and a concrete bound
on accepting a false result, all tied to the same final verifier. The proofs
connect FRI reasoning to Merkle checks and transcript-dependent challenges,
and handle adaptive prover choices, private randomness, repeated oracle calls
and bias in query sampling.

This integration yields the square-sequence guarantee stated above, with the
field and domain obligations and the numerical probability bound proved in
Isabelle. It also provides reusable proofs connecting adaptive Fiat–Shamir
execution to the staged soundness analysis. The [report](report/main.pdf)
gives a more detailed comparison; [PUBLICATION.md](PUBLICATION.md) states the
precise guarantees and their scope.

## ## Acknowledgements

Parts of this research were carried out using OpenAI's **ChatGPT for Academic Researchers** programme.

The formalization work uses the [Isabelle PIDE MCP server](https://github.com/kappelmann/isabelle-pide-mcp). Special thanks to Kevin Kappelmann for his generous support in answering questions about the MCP server.

Parts of the soundness proof, in particular the MCA approach, were inspired by [zkSecurity's simple-rbr-fri project](https://github.com/zksecurity/simple-rbr-fri). Thanks to Yoichi Hirai for providing a helpful overview of that work.

## License

This repository is distributed under the BSD-3-Clause license. See [LICENSE](LICENSE).
