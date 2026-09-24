# Lean protocol verification

This project now contains a **kernel-checked protocol safety proof and
conditional end-to-end liveness proof**, extending the original delivery-core
prototype. The larger Lean model includes quorum selection, tagged timeout
fallback, leader-only dispatch, physical response provenance, batching, a
separate deduplication cache, and leader failover with pending-request retries.
Its projection to the original delivery core is proved, not assumed.

The current goal is **paper-level correctness**, not verification of Raft or Go.
[PAPER.md](PAPER.md) maps the paper's claims to named Lean statements, including
Lemmas 1-2, Theorems 1-2, first-committed-response selection, batching equivalence,
race-order agreement, and deterministic continuations. It also records the
confirmed crash-stop scope and the application-observation boundary.

Recovery is out of scope: `CrashStop.lean` rules out rejoining failed replicas.
The primary results are `Paper.theorem_1_crash_stop` and
`Paper.theorem_2_crash_stop`. The broader recovery-capable library is retained
as supplementary work, not a requirement or assumption of the paper target.

Read [PROTOCOL.md](PROTOCOL.md) for the coverage matrix and the exact liveness
contracts. In particular, pending requests need fair proposal/re-proposal
attempts; consensus progress is required only for the eventual stable leader's
actual attempts. This is not a proof of Raft, the Go implementation, or the literal
TLA+ source. Nothing here connects to CloudLab or changes a running TLC job.

## Run it

From the repository root:

```sh
make fetch-lean    # one-time, isolated toolchain download
make check-lean    # build proofs/tests and enforce the axiom audit
```

The pinned version is **Lean 4.24.0**. The fetcher verifies the official release
archive's SHA-256, installs under ignored `tools/lean-*`, and makes no global
profile changes. It supports macOS/Linux on x86-64/ARM64. The archive is roughly
450 MB and the extracted macOS ARM64 toolchain is about 2.1 GiB. GNU tar may
need the `zstd` executable installed to extract `.tar.zst` archives on Linux.

An existing compatible Lean/elan installation also works. For a custom binary
directory, use `LEAN_BIN=/absolute/path/to/bin make check-lean`.
With elan, `cd lean && lake build` builds the project, but the recommended
`make check-lean` also runs `Audit.lean`. There are no Mathlib or other external
Lean package dependencies; all proofs use Lean's bundled standard library.

## Original delivery-core layer

Request IDs, response values, and replica IDs are type parameters, not enumerated
constants. Request IDs and replica IDs need decidable equality. The proof has
no fixed number of replicas/requests/responses, maximum log length, maximum
execution length, or maximum batch size. Each state has a finite log and each
reachable state is reached after finitely many transitions; the safety result
therefore applies to every finite prefix of an execution.

The model has independent state for:

- a shared consensus log of ordered response batches;
- each replica's set-like list of learned, zero-based slot indices;
- each replica's next slot to process; and
- each replica's delivered response sequence.

Executions start with empty state and consist of:

1. Appending an arbitrary batch to the consensus log.
2. Learning any already decided slot, in arbitrary order.
3. Processing **only the next slot**, if learned, using the actual batch at that
   log position. The handler checks request IDs and incrementally appends new
   responses to the replica's existing delivery history.
4. Stuttering (no state change).

The log may contain duplicate IDs with **different response values**, both
within and across batches. Thus agreement is not assumed by requiring a unique
response per ID in the log. The log is nevertheless one shared, append-only
sequence: consensus agreement and immutability are assumptions of this model.

`step_preserves_invariant` proves that every transition preserves:

- processed slots stay within the decided log;
- only decided slots are learned;
- every processed slot has been learned; and
- each delivery history is exactly `dedup(flatten(take(processed, log)))`.

`reachable_invariant` proves this for **every reachable state** by induction.
The last equality is a proved invariant, not a transition precondition or the
definition of the stored delivery field. `dedupFrom` is a separate reference
scan; `applyItems_eq_reference` connects the incremental batch handler to it.

From that invariant, `Safety.lean` proves:

- `at_most_once_delivery` / `delivery_count_le_one`: no request ID is delivered
  more than once by a replica.
- `response_agreement`: if two replicas deliver the same request, their
  response values agree.
- `prefix_agreement`: replica delivery histories are compatible prefixes.
- `race_winner_agreement`: nonempty histories have the same first request ID.
- `delivered_in_log`: every delivered item occurs in the consensus log.
- `step_delivery_monotone`: transitions cannot retract or replace delivered
  responses (proved directly for every step).

These core theorems are safety results only. `ProtocolLiveness.lean` and
`ProposalRetry.lean` add conditional liveness. The primary results are
`eventual_delivery_stable_consensus` and `exactly_once_stable_consensus`
(workflow delivery), under explicit ingress, handler/retry, stable-leader
consensus, learning, and processing assumptions. The older global-buffer
progress variant is retained for comparison, not required by these results.

## Correspondence to TLA+

The mapping to TLA+ below is an engineering correspondence, **not a
machine-checked translation**. The distinct mapping from the larger **Lean**
protocol to the Lean delivery core is proved by `Protocol.reachable_refines`.

- `consensusLog` maps to `State.log`; `DecideOne`/`DecidePair` map to `Step.append`.
- `LearnSlot` maps to `Step.learn` (TLA+ slot `i` maps to Lean slot `i - 1`).
- `ProcessContiguous` maps to `Step.process`.
- `ApplyItems` maps to `applyItems`; `DedupFrom` maps to `dedupFrom`.
- `AppliedPrefixCorrect`, `ProcessedWithinLog`, `LearnedOnlyDecided`, and
  `ProcessedPrefixLearned` map to the four `Invariant` fields.
- The corresponding agreement, uniqueness, and race invariants map to the
  exported safety theorems above.

The Lean abstraction deliberately differs in these ways:

- No `MaxSlots` bound or `PrioritizeUniqueDecisions` scheduling restriction.
- Any finite batch size, including empty batches, is allowed, not just one or two.
- Re-learning a slot is allowed, unlike the TLA+ guard. This adds harmless
  repeated learning actions without enabling skipping of gaps.
- The original core derives `seen` from delivered IDs; the **larger protocol**
  stores it independently. `applyCached_correct` and `reachable_cache` prove
  consistency and justify the core projection.
- Request quorum selection, payloads, dispatch, external execution, proposals,
  leader state, and crash/recovery are abstracted away in the original core,
  but are present in `Protocol.lean`. Arbitrary core log contents overapproximate
  the larger model's possible committed responses.

## Trust boundary and regression checks

All proof obligations are discharged. `make check-lean` treats warnings as errors
and audits every declaration in the `Resdet` namespace, including the named
regression tests. It rejects unfinished-proof axioms, native-evaluation trust
axioms, and any additional user axiom. The allowlist contains only Lean's usual
logical foundations (`propext`, `Quot.sound`, `Classical.choice`). The current
safety theorems actually depend only on `propext` and `Quot.sound`; liveness
also uses `Classical.choice` for ordinary classical reasoning.

`Tests.lean` supplies an explicit reachable two-replica execution with reordered
learning, conflicting duplicate responses, batching, and a lagging replica.
It also checks empty batches and duplicate slots. Broken-rule examples show
that removing deduplication duplicates deliveries, and that skipping a prefix
can disagree; conflicting-prefix and pre-consensus-delivery states are proved
unreachable in the correct model. All concrete checks use kernel reduction,
not native evaluation.

`CrashStopTests.lean` checks the current paper scope using three replicas: one
leader fails permanently, its successor retries the unfinished request, and
both survivors deliver once. The old leader's proposal need not commit. It
also supplies a behavior satisfying the crash-stop liveness premises jointly.

As supplementary checks, `ProtocolTests.lean` adds a crash/election/recovery execution with
different physical responses and checks that both replicas deliver the first
committed response. It includes a reachable counterexample to once-only physical
dispatch with failures, a tagged timeout fallback, a forever-stalled behavior
showing why fairness is needed, and a non-vacuity proof that all the liveness
contracts are jointly satisfiable on an extension of the recovery execution.
`reproposal_reachable` checks the new retry action, and
`retry_contracts_satisfiable` checks the primary liveness premises jointly.

The trusted base still includes Lean's kernel and standard library environment.
An axiom audit does not establish that the formal definitions faithfully model
the paper or the Go code. Those definitions and the correspondence need review.

## Scope boundaries

- A mechanically checked translation from `Resdet.tla` or refinement of the Go
  code is outside the current paper-level goal.
- All process recovery/rejoin behavior, including deduplication-state restoration,
  is outside the author-confirmed crash-stop scope.
- Real-runtime progress guarantees and Raft correctness are outside the current
  goal. Unfinished-request retries are explicitly part of the paper model.
- Durable storage mechanisms or exactly-once external side effects.

The modeled safety obligations are proved, and the conditional liveness theorem
is proved. Remaining work concerns model fidelity and assumption discharge,
not filling in unfinished Lean proofs. This is not an unconditional claim that
every behavior of the Go implementation satisfies the paper's theorems.

## Sources

- [Pinned Lean release](https://github.com/leanprover/lean4/releases/tag/v4.24.0)
- [Lean induction](https://lean-lang.org/theorem_proving_in_lean4/Inductive-Types/)
- [Proof validation and axiom auditing](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
