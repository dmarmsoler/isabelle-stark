# Current results and publication scope

This is the short entry point to the current Isabelle/HOL development. The
technical report and older audits retain the development history; this overview
does not replace their evidence. For checking instructions and remaining artifact
release gates, see [REPRODUCING.md](REPRODUCING.md).

The minimal release retains the complete theory-import closure of the ten-result
publication manifest and the executable [Square Sequence example](Examples/Square_Sequence.thy):
487 theories in total. All retained theory sources are unchanged. The 84 removed
theories and validation evidence are recorded in the [cleanup audit](audit/minimal_public_release.md).
Historical report and audit references to omitted theories refer to the full
development at Git revision `0fcbf9ff3282b7043142f1c7f3999070917b55ec`.

## Principal result

For fixed endpoints `a,z` in the certified 192-bit prime field, the square
workload represents `z = a^(2^1023)`: its trace contains 1024 values, hence 1023
squarings. The concrete instance uses scale 64, two shifted trace powers and
640 query repetitions.

- If that endpoint equation holds, the specified honest producer is accepted
  with probability one in the absorbing random-oracle experiment.
- If it does not hold, every program in the modeled adaptive/private
  Fiat–Shamir language making at most `2^20` oracle calls has acceptance
  probability at most `2^-137`.

These are Isabelle-certified results about the same final verifier, with
different honest and malicious producer interfaces. The malicious theorem has
exactly two exported premises: the incorrect endpoint and `fs_query_bound (2^20) P`.
Its concrete field/domain/workload obligations are discharged, not additional
public soundness assumptions. Generic results retain their locale predicates.

## Claim-to-theorem map

Names below are also selected by the build-checked
[Publication_Manifest](Soundness/Publication_Manifest.thy). It exports the actual
statements and dependency information; this table is an explanation, not a
substitute for those statements.

| Claim | Theory and theorem | Important boundary |
|---|---|---|
| Workload means the endpoint equation | [Square_Sequence_192_Core_Completeness](Soundness/Square_Sequence_192_Core_Completeness.thy), `square_192_valid_trace_iff` | An equivalence, not merely an uninterpreted validity predicate |
| Honest RO acceptance is one | [Square_Sequence_192_RO_Completeness](Soundness/Square_Sequence_192_RO_Completeness.thy), `square_ro_honest_experiment_acceptance_one` | Correct endpoint is the sole premise; no honest budget-fit claim |
| Honest/staged and FS interfaces use the same final verifier | [FS_Adversary_Model](Soundness/FS_Adversary_Model.thy), `soundness.staged_fs_verifier_factorization` | Producer interfaces remain different |
| Fixed-private-choice adaptive producer embeds exactly | [FS_Adaptive_Staged_Embedding](Soundness/FS_Adaptive_Staged_Embedding.thy), `soundness.fs_compile_replay_acceptance` | Oracle-query continuations remain adaptive |
| Private randomness also transports exactly | Same theory, `soundness.fs_compiled_mixture_acceptance` | A mixture of whole compiled programs, not independent choices at callbacks |
| Replay compiler has an explicit sufficient allowance | [FS_Replay_Allowance](Soundness/FS_Replay_Allowance.thy), `soundness.fs_replay_total_allowance` | Not a minimum allowance or equality with actual producer calls |
| Complete conventional-Q bound | [FS_First_Root_Soundness](Soundness/FS_First_Root_Soundness.thy), `soundness.fs_first_root_soundness` | Includes existing locale and false-statement/query-cap premises |
| Exact improvement over preceding ledger | [FS_Square_First_Root_Comparison](Soundness/FS_Square_First_Root_Comparison.thy), `square_fs_first_root_ledger_balance` | Identity between upper bounds, not actual success probabilities |
| Closed certified numerical inequality | [FS_Square_192_137](Soundness/FS_Square_192_137.thy), `square_fs_137_prefix_target` | Proved rational/arithmetic estimate, not a Python calculation |
| Concrete false-endpoint acceptance bound | Same theory, `square_192_fs_137_incorrect_endpoint` | Fixed statement; `Q <= 2^20`; acceptance at most `2^-137` |

To expand the generic assumptions, follow `soundness` in
[Soundness_Core_Base](Soundness/Soundness_Core_Base.thy), its parent `verifier`
and `stark` locales in [Core/Stark](Core/Stark.thy), and the field class used
there. In the concrete endpoint, `square_192_soundness` in
[Soundness_Square_Sequence_192](Soundness/Soundness_Square_Sequence_192.thy)
discharges that locale from proved field/domain/workload facts and the positive
repetition count, instantiated by 640. The manifest retains the one locale
premise on the generic factorization and replay-allowance equalities; it does
not turn those generic statements into unconditional ones.

## What the adversary and oracle mean

`FS_Query` permits an arbitrary continuation depending on the oracle answer.
`FS_Sample` permits private finite-support choices; later actions can depend on
previous choices and answers. The language describes terminating classical
computations, not quantum queries or general countably supported executions.
The cap is a uniform bound over program continuations, not an expected number
of calls. A repeated/cached query costs another call. The producer outputs a
purported transcript and the original verifier runs against the same oracle map.

The oracle is a typed, domain-separated, lazy field-valued random oracle. The
result does not establish the correspondence to a particular bit-hash encoding
or implementation. Statements are fixed before the experiment; the theorem is
not an adaptive-statement or multi-instance security result.

The compiler replays the producer at staged callbacks. Its sufficient declared
allowance is `(trace_depth + maximum_composition_depth + R + 4) Q`, equal to
`664 Q` for the concrete 640-repetition instance. This is an operational compiler
cost. Event-sensitive probability proofs can charge a single producer execution
without changing that operational allowance or making cached calls free.
No equality of the two attacker classes at the same allowance is claimed.
Private normalization is a semantic finite-mixture theorem, not a claimed
polynomial-time enumeration or implementation of that mixture.

## Quantitative result and proof mechanisms

The generic complete first-root bound retains the old fallback. For the square
640-repetition regime its source-connected ledger is

```
E_first(Q) = (21 Q^2 + 2464458513 Q + 8773058386762) / (2 F)
          + (Q + 914610) * (p(54953)^640 + 2 p(54954)^640)
p(B)      = ((F div 65472) B + min(B, F mod 65472)) / F
```

Here `F` is the field cardinality, and `p` is the exact maximum modulo-preimage
envelope, not a claim that query indices are uniformly distributed. The query
space has 65,472 indices; the evaluation domain has 65,536 points.

The checked ledger improvement is `(5296 Q^2 + 3206956 Q) / F`. The established
integer-bit certificate remains `2^-137`, proved using the preceding prefix
ledger. External evaluation of the stronger first-root ledger gives about
138.836299 bits at `Q=2^20`; this is not a separately certified 138-bit theorem.
Neither upper bound is an attack probability or a proven work factor.

Three mechanisms provide the central paper narrative:

1. Composition of algebraic FRI reasoning, authenticated openings, exact
   sampling, transcript operations and an executable probabilistic verifier.
2. Acceptance-preserving adaptive FS transport through the established staged
   interface, including private randomness and a precise operational allowance.
3. Weighted-path and event-sensitive accounting retaining the full sampling
   exponent, plus saved-prefix target bounds without assuming independence or
   subtracting event overlap only on successful executions.

FRI folding rounds, query repetitions, individual layer openings and producer
oracle calls are different quantities. The final verifier shares the relevant
commitment/challenge lists across its sequential query rounds. Do not equate
640 query repetitions with 640 independent complete FRI commitment phases.

## Deliberate limits

- No zero-knowledge simulation, knowledge extractor, QROM theorem, deployed
  hash/code refinement, general workload efficiency theorem or priority claim.
- The certified large-field generator is chosen by Hilbert choice from proved
  existence. This is a concrete mathematical instance, not an extracted runnable
  192-bit implementation with an explicit generator numeral.
- The honest-callback allowance obstruction concerns all-state staged control.
  It is not a lower bound on ordinary honest calls, a universal producer
  impossibility, or a contradiction with the malicious FS query cap.
- Earlier near-64k diagnostics and restricted-slice exclusions do not prove a
  universal realizability ceiling or substantially smaller true maximum.
- Empty theorem oracle lists do not eliminate the HOL foundational basis or
  establish correspondence between definitions and an intended deployed system.

The development supports paper preparation now. Exact dependency downloads are
verified and checksum-pinned; [REPRODUCING.md](REPRODUCING.md) distinguishes the
successful isolated same-host build from independent clean-machine reproduction.
The latter, independent semantic review and a current revision-pinned
related-work comparison remain publication-release work.
