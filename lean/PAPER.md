# Verification scope: the paper, not Raft or Go

Source reviewed: `MicroserviceReplication.pdf`, titled *Cyclades: Taming
Nested-Response Nondeterminism in Replicated Microservices*, 15 pages, as supplied
on 2026-09-23. The PDF is unchanged. Reviewer annotations are not proof claims
or instructions. This document concerns the protocol-correctness claims, not
experimental throughput/latency results or historical claims about other systems.

The target is the paper's Resdet/EO algorithm and its Cyclades extensions,
assuming its consensus and environment contracts. **Proving Raft or verifying
the Go program is not required to complete this target.** Those are excluded
layers, not missing deliverables.

**Author-confirmed scope (2026-09-23): recovery is out of scope; unfinished
requests retry.** The primary paper interface is therefore crash-stop:
failed replicas do not rejoin, a surviving leader handles retries with the same
logical request ID, and delivery liveness is required only for non-faulty
replicas. This clarification supersedes the broader recovery wording in the
previous PDF/model discussion. It does not remove failures or leader changes.
The supplied PDF itself has not been edited.

## Claim-to-proof map

Names below are in `Resdet.Paper` unless another namespace is specified.
These are general proofs, not bounded example checks.

| Paper claim | Checked result | Boundary |
| --- | --- | --- |
| Section 5.2, Lemma 1: same processed index, same entry | `lemma_1_same_processed_entry` | CG1 is represented by a common immutable committed log; both local processed histories contain the entry and both replicas learned it |
| Section 5.2, Lemma 2: no-hole processing | `lemma_2_no_hole_processing` | Uses the inductive core invariant; slots are zero-based rather than the paper's one-based indexes |
| Theorem 1: response agreement | `theorem_1_crash_stop` (via `theorem_1_safety`) | Covers deliveries by different replicas at different times, not just a simultaneous snapshot |
| Section 5.3, step 1: eventual agreement | `eventually_agreed` | Stable leader, eventual ingress, pending-handler/retry fairness, CG3 proposal progress |
| Section 5.3, step 2: eventual prefix learning | `eventually_prefix_learned` | Finite-prefix induction using CG3 learning and persistent learned state |
| Section 5.3, step 3: prefix processing and delivery | `Resdet.eventually_processed`, `eventually_delivered` | Local processing progress (L4); duplicate suppression cannot remove every occurrence of an ID |
| Theorem 2: every submitted request reaches every non-faulty replica | `theorem_2_crash_stop` (via `theorem_2_liveness`) | Core Resdet, quorum one; unfinished requests retry; failed replicas need not deliver |
| Sections 4.2-4.3: deliver only once, and choose the first committed response despite conflicting retries | `first_committed_response`, `Protocol.at_most_once_delivery` | Arbitrary conflicting values and batches; surviving replicas retain their running state |
| Section 3.3: common winner for a fan-out race | `race_winner_for_group` | Any common set of competing IDs; the application must use the agreed delivery order as its observation order |
| Sections 3.3/6.3: deterministic continuations agree after shared inputs | `deterministic_continuation` | Same initial application state and deterministic transition function; compare equally long consumed prefixes |
| Section 4.2: only leader dispatches; physical responses do not bypass commitment | `Protocol.only_leader_dispatches`, `Protocol.response_validity`, `Protocol.all_safety.noEarlyDelivery` | The recorded leader at dispatch time; no promise of once-only external effects |
| Section 6.1: matching distinct-voter quorum on normal path | `Protocol.selection_justified`, `Protocol.strict_quorum` | Payload correctness is not implied by a quorum; timeout path explicitly excluded from strict-quorum assertion |
| Section 6.1: force-yield can make progress without a quorum | `fallback_arrival_ready` with `eventually_delivered` | Fallback enabled, at least one received request, fair selection/handlers; no promise that arbitrary fallback chooses a semantically correct request |
| Section 6.2: batching preserves safety | `batching_equivalent`, `rebatching_preserves_delivery` | Actual incremental batch processing equals a flattened ordered scan; re-grouping preserves results when it preserves entry order |
| Section 8: external calls may execute more than once | `CrashStopTests.retry_can_repeat_external_execution`, `CrashStopTests.failover_retry_run` | Reachable failover/retry trace with no recovery |
| Author-confirmed exclusion of recovery | `CrashStopBehavior.permanently_down`, `CrashStopBehavior.stable_leader_nonfaulty` | Once down, always down; the stable leader is a survivor, not a recovered replica |

`theorem_2_crash_stop` proves a slightly stronger conclusion than Theorem 2: for
each submitted request and qualifying replica, some value is eventually in its
delivery history **at every later time**, with that request's delivery count
equal to one. `theorem_1_crash_stop` ensures the value agrees across replicas.

The original singleton-entry protocol is a special case of the batched model.
`PaperTests.batch_boundaries_do_not_change_result` also checks a concrete trace
with conflicting duplicates, different batch boundaries, and an empty batch.
Batching equivalence does not say arbitrarily reordering entries is harmless:
reordering conflicting responses can change the first winner.

## Assumptions, not proof targets

- **CG1/CG2:** a shared immutable append-only consensus log represents slot
  agreement and prefix commitment. No consensus implementation is analyzed.
- **CG3(1):** `Protocol.StableLeader` states eventual stable live leadership.
- **CG3(2):** `Protocol.StableConsensusProgress` guarantees agreement only for
  actual attempts by that leader after stabilization. It does not require every
  old leader's buffered proposal to commit.
- **L1/L2:** the core theorem has a `submitted` predicate and an explicit eventual
  arrival premise for each submitted ID. Forwarding/network queues are abstracted
  into that premise; transport is not implemented in the Lean transition system.
  `single_arrival_ready` proves that this needs only one arrival for core Resdet,
  not the stronger Cyclades quorum gate.
- **L3/L4:** `PendingHandlers` specifies per-request progress through selection,
  dispatch, response, and proposal attempts while the request is not agreed.
  These premises do not assume agreement or delivery. Unfinished requests retry
  through the eventual stable leader; no failed process must resume its handler.
- **CG3(3)/L4:** `DeliveryProgress` specifies eventual learning and fair
  next-slot processing. Whole-prefix processing and eventual delivery are proved,
  not included as premises.
- **Identifiers and payloads:** the paper assumes the same logical call has the
  same ID and body and retries reuse them. These are application-interface
  assumptions; no ID generation algorithm is claimed to be verified.
- **Fault bound:** the paper's `n = 2f+1` and at most `f` unavailable replicas
  justify obtaining the consensus progress contract from a consensus service.
  Once that contract is assumed, the Resdet proofs need no fixed replica count.
- **Crash-stop:** `CrashStopBehavior` restricts the general protocol behavior so
  a node that becomes down remains down at every later time. `NonFaulty` means
  the node never goes down. A restarted process, state restoration, and recovery
  of deduplication state are excluded, not extra assumptions of the paper proof.
  Historical state of failed nodes remains as bookkeeping, not as a mechanism
  for restarting them.

`CrashStopTests.crash_stop_contracts_satisfiable` supplies an actual three-node
behavior with one failed leader, two non-faulty survivors, a retried request, and
the progress contracts jointly satisfied. The failed leader never returns and
its old response proposal remains uncommitted; both survivors deliver the new
leader's committed response once. This excludes simple contradictory-premise
vacuity; it is not a proof that every environment satisfies the contracts.

## Paper text alignment

### 1. Include L4 in Theorem 2

The theorem statement in section 5.3 lists CG2-CG3 and L1-L3, but its proof
repeatedly invokes L4. Its assumptions should include L4 explicitly. An infinite
behavior can learn an entry and never process it without local progress; the
existing `Protocol.Tests.fairness_is_necessary` checks that distinction.

### 2. State crash-stop failures and retries (resolved by the author)

Suggested scope wording, matching the confirmed model:

> We consider crash-stop failures: a failed replica does not recover or rejoin
> during the execution under consideration. Unfinished logical requests retry
> with the same request ID and body through the eventual stable leader. Liveness
> applies to non-faulty replicas. Process recovery and restoration of local
> protocol state are outside scope.

The recovery-marker counterexample from the earlier review is **not a blocker**
for this scope. That counterexample requires a failed replica to restart, which
`CrashStopBehavior` forbids. The optional broader recovery model and its tests
remain in the library, explicitly separate from the paper target. No recovery
protocol, leadership-epoch reset, or durable handler resumption is requested.

`Step.repropose` continues to express a proposal retry by a live leader. It does
not restart a failed process. `PendingHandlers` requires fair progress only
while the request has no committed response, not redundant physical execution
of an already completed request.

### 3. State the application-consumption boundary of the race claim

`race_winner_for_group` proves agreement on the first eligible item in the common
delivery order. If application code asynchronously schedules awakened handlers
and then chooses an unrelated scheduling winner, common delivery order alone
does not constrain that choice. The paper's `wait_any` claim should specify that
the agreed order is the order observable by the race primitive. Similarly,
`deterministic_continuation` does not claim to repair arbitrary concurrency bugs,
which section 8 already excludes.

## Completion criterion and reproduction

All named Lean statements above have checked proofs with no unfinished-proof
axioms. Recovery is excluded and is no longer an unresolved scope choice.
The paper text should align with that scope, include L4 in the liveness theorem,
and specify the observable delivery-order contract for the race claim. These are
paper/model correspondence points, not requests to verify Raft or Go.

An accurate summary is **"machine-checked safety and conditional liveness for
Resdet under crash-stop failures and pending-request retries, with consensus
assumed as a black box."** This does not assert that every empirical claim or
every possible reading of the earlier PDF has been proved.

Run `make check-lean` to build the proofs, regression examples, and transitive
axiom audit. Nothing in this target accesses CloudLab or launches a TLC job.
Experimental findings in section 7, comparative claims about Aegean/Eve, and
related-work statements retain their experimental/literature evidence; they are
not converted into Lean theorems by this verification.
