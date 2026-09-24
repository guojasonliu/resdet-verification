# Resdet/EO verification: TLA+ and Lean

This repository contains a small, executable TLA+ model of the Resdet/EO
protocol from *Cyclades: Taming Nested-Response Nondeterminism in Replicated
Microservices*.

The model targets the protocol implemented as `eo` in `aegean-clone`. It
checks the novel layer above an abstract total-order consensus service instead
of attempting to verify etcd/Raft itself.

## Lean protocol proofs

The target is the **paper's protocol-correctness claims**, with consensus kept
as its black-box assumption. [Paper coverage](lean/PAPER.md) maps Lemmas 1-2,
Theorems 1-2, batching, and related claims to checked proofs and identifies
remaining clarifications in the paper. The confirmed failure model is crash-stop:
failed replicas do not rejoin, and unfinished requests retry through a surviving
leader. Raft/Go verification and process recovery are outside scope.

The [`lean/`](lean/README.md) companion now contains parameterized protocol-level
safety proofs, a proved mapping to the delivery core, and conditional end-to-end
liveness/exactly-once workflow-delivery proofs. It includes quorum selection,
tagged fallback, dispatch/response validity, a separate seen cache, and
crash-stop failover/retries. The older recovery extension is supplementary.
It is not bounded to five replicas or ten requests.

Read the [coverage and assumptions](lean/PROTOCOL.md): consensus safety remains
abstract, and liveness requires explicit progress contracts including fair
proposal/re-proposal attempts. The primary theorem only requires consensus
progress for actual attempts by the eventual stable leader, not all old buffered
proposals. Neither the Go code nor a literal translation of the TLA+ source has
been verified.

```sh
make fetch-lean     # one-time project-local Lean 4.24.0 installation
make check-lean     # proofs, concrete examples, and a strict axiom audit
```

This is a separate local check; it does not launch, stop, or modify any TLC run.
The existing `make check` and research profiles below remain TLA+-only.

## Quick start

Java 11 or newer and `curl` are required. The runner downloads the immutable
official TLA+ Tools 1.7.4 release and verifies its SHA-256 digest. It does not
use the moving 1.8.0 prerelease asset, which upstream replaces on new builds.

```sh
make check
```

The default models are intentionally small. They are smoke checks suitable
for iteration. This is the **prototype scale**, not the final research-scale
run.

Useful subsets:

```sh
make check-passing
make check-mutants
```

You can also provide an existing tools JAR:

```sh
TLA2TOOLS_JAR=/path/to/tla2tools.jar ./scripts/check.sh all
```

## What is modeled

`spec/Resdet.tla` represents:

1. Service replicas submit or forward a deterministic nested request.
2. The EO leader accepts it; the Aegean integration may first require a
   matching caller quorum.
3. Only the leader sends the physical downstream request.
4. The external service may return any modeled response value.
5. The leader proposes the response to a total-order consensus box.
6. Consensus slots may contain one response or an ordered response batch.
7. Replicas may learn decided slots out of order.
8. Each replica processes only its contiguous learned prefix.
9. Duplicate request IDs consume their slot but are not delivered twice.
10. A workflow race chooses the first request ID in the delivered order.

The consensus log is global and append-only. That is the contract supplied by
Raft; this model verifies Resdet's use of that contract.

The request-vote state covers two related paths. With `Quorum = 1` it models
the paper's `handle_request`/`forward` path: one invocation reaching the
leader is sufficient. With `Quorum = 2` it models the matching caller-side
gate added by the Aegean implementation.

## Checked properties

The passing configurations check:

- quorum justification for normal request selection;
- explicit identification of timeout-fallback selections;
- no dispatch before request selection;
- leader-only dispatch in the strict model;
- validity from physical execution through proposal and consensus;
- at-most-once physical dispatch when the leader remains stable;
- at-most-once workflow delivery per request ID;
- response agreement between replicas;
- compatible delivered prefixes;
- contiguous learned-slot processing;
- equivalence to the deduplicated consensus-log prefix;
- validity of every delivered response;
- agreement on the winner of a response race; and
- eventual completion under a stable leader and weak fairness.

## Prototype-scale configurations

| Configuration | Purpose | Expected |
| --- | --- | --- |
| `ResdetCore.cfg` | Paper protocol with one forwarded invocation sufficient | Pass |
| `ResdetStrict.cfg` | Aegean's matching 2-of-3 caller quorum integration | Pass |
| `ResdetBatching.cfg` | Two request IDs, two-item batches, race ordering | Pass |
| `ResdetFailures.cfg` | Crash/recovery and re-election; delivery safety only | Pass |
| `ResdetFallback.cfg` | Timeout fallback with a documented non-quorum selection | Pass |
| `ResdetLiveness.cfg` | Stable-leader progress under weak fairness | Pass |

The prototype liveness model sets `PrioritizeUniqueDecisions = TRUE`. This is
a bounded scheduling assumption: while an as-yet undecided request has a
proposal, its first decision is chosen before retry entries can consume the
finite log. The prototype safety configurations leave this disabled and
explore arbitrary retry order.

## Research-scale profile

`ResdetResearch.cfg` scales the core safety model to:

- five replicas with a 3-of-5 quorum;
- ten logical request IDs;
- two nondeterministic response values;
- response batching;
- ten consensus slots; and
- the complete normal-path safety invariant set.

It intentionally keeps a stable leader and one request-payload variant.
Crash/recovery, split request payloads, timeout behavior, and temporal
liveness remain in the focused prototype configurations. This layered
approach increases the important width and ordering dimensions without
multiplying every feature into one intractable state space.

For a quick research-scale sanity check, run randomized simulation:

```sh
make check-research
```

The default samples 50 traces of depth 250 with a fixed seed. Override these
without changing the configuration:

```sh
TLC_SIM_TRACES=10000 TLC_SIM_DEPTH=2000 make check-research
```

Simulation checks every invariant along the sampled traces, but it is **not
exhaustive verification**. For an exhaustive breadth-first run, use:

```sh
TLC_HEAP=16g TLC_WORKERS=auto make check-research-exhaustive
```

The exhaustive command is deliberately excluded from `make check`. It writes
checkpoint metadata under `.tlc/` and may take substantial time. The research
profile uses `PrioritizeUniqueDecisions = TRUE` so each newly proposed request
gets a first log position before retries can fill the bounded ten-slot log;
the prototype safety suite separately explores arbitrary retry ordering.

### Fresh CloudLab node

For **sm220u with Ubuntu 22.04 or 24.04**, use the standalone
`scripts/setup-sm220u.sh` instead of the boot-disk helper below. It can be saved
anywhere (including `~/setup.sh`) and locates or clones the repository under
`~/resdet-verification`. Start with its read-only inventory:

```sh
bash scripts/setup-sm220u.sh --inspect
```

If a large filesystem is already mounted at `/mnt/tlc`, run
`bash scripts/setup-sm220u.sh --start`. Otherwise, after identifying six to eight unused
whole NVMe namespace devices, pass their **explicit paths** to
`bash scripts/setup-sm220u.sh --setup ...`. Preparation refuses disks with existing
signatures, partitions, mounts, or holders and requires `PREPARE` before
initializing them. It creates an LVM stripe across the selected drives using 95% of capacity,
formats ext4, and mounts it at `/mnt/tlc`. The stripe has no redundancy.

Both setup and start install dependencies, verify a separately named TLC
1.7.4 JAR, run a two-trace smoke test, and **launch the exhaustive run** in
Screen `resdet`; do not invoke a second `make` command. Defaults are 140g heap
and 32 workers. Each unique `/mnt/tlc/resdet/research-*` directory contains
frozen model/JAR inputs, checksums, settings, the Java PID, `tlc.log`, and
`states/` checkpoint data. Startup is reported only after Java is alive and
TLC has computed initial states. Arrange a consistent off-node checkpoint
backup before expiration; no external backup destination is configured by
this script. These local disks are lost when the experiment expires.

The actual six-drive provisioning command and run location for
`sm220u-10s10541` are recorded in
[`scripts/sm220u-setup-record.md`](scripts/sm220u-setup-record.md).

Launcher refusal/shutdown tests (no disks are formatted):

```sh
python3 -m unittest discover -s tests -p 'test_sm220u_setup.py'
```

On a fresh CloudLab node with a large local disk (the `r7525` profile uses
`/dev/sda`), clone the repository and run:

```sh
git clone https://github.com/guojasonliu/resdet-verification.git
cd resdet-verification
./scripts/cloudlab-research.sh
```

The script installs any missing Java, `curl`, and GNU Screen packages;
prepares and mounts unused local storage at `/mnt/tlc`; downloads and verifies
the pinned TLC release; chooses conservative heap and worker defaults; and
starts the exhaustive check in a detached Screen session named `resdet`.
Before creating and formatting the unused partition, it requires the literal
confirmation `PREPARE`. It will reuse a mounted filesystem and will not
reformat a partition with a recognized filesystem.

Attach with `screen -r resdet`. Detach with `Ctrl-A`, then `D`. The script
prints the exact log path and disk-monitoring command when it launches. Local
CloudLab storage is ephemeral, so copy the log elsewhere before terminating
the experiment.

## Paper theorem correspondence

The paper's two headline theorems map directly to TLC checks:

- **Theorem 1, Safety:** non-faulty Resdet replicas never deliver different
  responses for the same logical request. This is `ResponseAgreement`,
  strengthened by `AtMostOnceDelivery`, `PrefixAgreement`, and
  `AppliedPrefixCorrect`.
- **Theorem 2, Liveness:** every submitted logical request is eventually
  delivered at each non-faulty replica. This is `Completion` under
  `FairSpec`.

The consensus assumptions CG1 (index agreement) and CG2 (prefix agreement)
are represented by one immutable global consensus log. CG3 (consensus
liveness), request-submission liveness, network liveness, downstream-service
liveness, and local-execution liveness are represented by weak fairness in
`FairSpec`. Safety configurations do not assume fairness.

Message delays and reordering appear as arbitrary action order and
out-of-order `LearnSlot` steps. A message may be delayed forever in a safety
run; the liveness run's fairness assumptions exclude permanent loss between
non-faulty components.

The mutant configurations are expected to fail. `scripts/check.sh` treats the
specific counterexample as success:

| Mutant | Removed rule | Expected violated invariant |
| --- | --- | --- |
| `NoDedup.cfg` | Request-ID duplicate suppression | `AtMostOnceDelivery` |
| `NonContiguous.cfg` | Contiguous-prefix processing | `ProcessedPrefixLearned` |
| `AllDispatch.cfg` | Leader-only physical dispatch | `AtMostOnePhysicalDispatch` |
| `NoQuorum.cfg` | Matching caller quorum | `SelectionJustified` |
| `EarlyDelivery.cfg` | Consensus before workflow delivery | `AppliedPrefixCorrect` |
| `NoLeaderDirect.cfg` | EO ordering while no leader is known | `ResponseAgreement` |

## Exact-once boundary

The model intentionally distinguishes three claims:

- **Exactly-once workflow delivery:** preserved across duplicate proposals,
  duplicate slots, out-of-order learning, and modeled leader changes.
- **At-most-once physical dispatch:** checked only when the EO leader remains
  stable.
- **Exactly-once external side effects:** not guaranteed if a leader performs
  an external effect and crashes before the response becomes durable in the
  consensus log. A new leader may have to execute the request again.

Thus the model does not claim transactional exactly-once behavior for an
arbitrary non-idempotent external service.

## Relationship to the Go implementation

| TLA+ concept/action | Go implementation |
| --- | --- |
| `SubmitVote`, `SelectByQuorum`, `TimeoutSelect` | `src/aegean/exec/nested_request_quorum.go` |
| `Dispatch`, `NoLeaderDispatch` | `src/aegean/exec/nested_dispatch_eo.go` |
| `ProposeResponse` | `EO.ProposeResponsePayload` in `src/eo/eo.go` |
| `DecideOne`, `DecidePair` | `src/eo/raft_box.go` plus EO response batching |
| `LearnSlot`, `ProcessContiguous` | `EO.LearnBatch`, `EO.Process`, and `dequeueCommittableEntries` |
| request-ID `seen` set | `EO.committedRequests` |
| `delivered` | EO commit callback into Aegean Exec or SMR |
| `RaceWinner` | first-ready nested-response workflows in Hotel and Online Boutique |

The Go performance setting `eo_disable_follower_elections` is deliberately
not used by the strict model. It is an experiment-only optimization, not a
safety mechanism.

The optional crash/recovery extension assumes that a recovered replica
retains its local learned and delivered state, and the consensus log remains
durable. The current Go prototype's `raft_box` uses etcd `MemoryStorage`, so
these checks are not evidence that the implementation itself survives process
restart without an added durable-storage/recovery path.
This extension is outside the author's current crash-stop paper scope; the
primary Lean results exclude recovery rather than requiring this persistence.

`TimeoutSelect` nondeterministically chooses any payload observed before the
timeout. This overapproximates the Go implementation's deterministic
lexicographic fallback and keeps the agreement proof independent of that
particular tie breaker.

## Scaling the final run

Treat the existing profiles as two evidence levels:

1. `make check` exhaustively checks the small **prototype scale**, including
   failures, fallback behavior, liveness, and counterexample mutants.
2. `make check-research-exhaustive` attempts exhaustive checking of the
   broader 5-replica/10-request **research scale**.

If the full research profile is too large, copy its configuration and grow
one dimension at a time while retaining completed-run results:

1. Increase `MaxSlots` to exercise longer duplicate histories.
2. Add request IDs to increase race width.
3. Add payload variants to explore split caller votes.
4. Add response values to explore more nondeterministic outcomes.
5. Enable batching with the larger request set.
6. Run with multiple TLC workers only after the one-worker liveness check.

Direct TLC equivalent of the supplied research-scale run:

```sh
cd spec
java -Xmx16g -jar ../tools/tla2tools.jar \
  -workers auto \
  -checkpoint 10 \
  -config ResdetResearch.cfg \
  Resdet
```

TLC model checking is exhaustive only within the finite constants in the
selected configuration. Passing these models is strong evidence for those
bounds, not a machine-checked general theorem and not direct verification of
the Go binary.
