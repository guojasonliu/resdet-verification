# Protocol-level proof scope and coverage

The verification target is the paper's correctness claims, **not** Raft or the
Go implementation. See [PAPER.md](PAPER.md) for the paper-to-theorem map, the
named Lemmas 1-2/Theorems 1-2, batching equivalence, and the remaining paper
clarifications. The author excludes recovery and specifies unfinished-request
retries. `Paper.theorem_2_crash_stop` restricts the general liveness proof to
non-rejoining failures and uses pending-only handler fairness. The broader
protocol-layer variants below remain useful building blocks and extensions.

## Results

`Protocol.all_safety` proves a bundle of normal-protocol safety properties for
every state reachable under `Protocol.Step`, including histories with crashes,
recovery, re-election, timeout selection, conflicting response values, duplicate
log entries, arbitrary batching, and reordered learning. Mode-specific
properties keep their conditions: timeout selections need not have a quorum,
and at-most-once physical dispatch is proved only with crashes disabled.

`Protocol.eventual_delivery_stable_consensus` proves that each admitted logical
request eventually has a response delivered at each replica satisfying the
progress contracts. `Protocol.exactly_once_stable_consensus` combines this with
safety to prove that the request's delivery count eventually equals one.
The at-most-once invariant
continues to hold at every later reachable state; responses cannot be retracted.
Neither theorem promises once-only external execution or side effects.

The older `eventual_delivery` / `eventual_exactly_once` variant assumes progress
for every globally buffered proposal and is retained for comparison. The primary
stable-leader theorems do not depend on that stronger consensus contract.

The proof is parameterized by replica, request, payload, and response types and
has no fixed state-space or execution-length bound. It does not enumerate
executions. Concrete regression traces are separate from these general proofs.

## Model and refinement

`Protocol.lean` models votes, one-time selection, dispatch, nondeterministic
external responses, response proposal/re-proposal attempts, consensus appends, learning, processing,
crashes, recovery, elections, and stuttering. Normal selections carry a checked
certificate of distinct matching voters of at least `Config.quorum` size.
Timeout fallback is separately enabled and tagged, requiring at least one vote.
No unsafe no-leader direct-delivery action is allowed.

The protocol maintains a separate `seen` list. `applyCached_correct` proves that
its incremental handler agrees with the core handler when the cache is coherent.
`step_cache` proves every action preserves coherence. `step_refines` proves
every protocol step projects to a delivery-core step (possibly stuttering), and
`reachable_refines` proves the projection is reachable. Safety is transferred
through this proved mapping and supplemented with protocol-specific invariants.

Consensus is still an abstract shared, immutable, append-only log. This supplies
the paper's CG1/CG2 safety contract; Lean does not re-prove Raft. In the broader
library, crash/recovery preserves protocol histories. The current paper target
excludes recovery entirely: `CrashStopBehavior` requires failed replicas to stay
down. Retaining their historical events is bookkeeping, not a restart protocol
or a durable-storage assumption.

## Safety correspondence to the TLA+ checks

The correspondence is manually reviewed, not a proved translation of TLA+
semantics. All names below are in namespace `Resdet.Protocol` unless indicated.

| TLA+ obligation | Lean result or encoding |
| --- | --- |
| `TypeOK` | Typed state fields; log/learned/processed bounds from the core invariant; finite `MaxSlots` bound intentionally removed |
| `SelectionJustified` | `selection_justified` |
| `StrictQuorumOnly` | `strict_quorum`, when timeout fallback is disabled |
| `NoDispatchBeforeSelection` | `no_dispatch_before_selection` |
| `OnlyAuthorizedDispatch` | `only_leader_dispatches`, using the recorded leader at dispatch time |
| `ObservedHasPhysicalExecution` | `observed_executed` plus `executions_dispatched` |
| `ProposalValidity` | `proposal_validity` |
| `ConsensusValidity` | `consensus_validity` |
| `AtMostOnePhysicalDispatch` | `at_most_one_physical_dispatch`, with crashes disabled |
| `AtMostOnceDelivery` | `at_most_once_delivery` |
| `ResponseAgreement` | `response_agreement` |
| `PrefixAgreement` | `prefix_agreement` |
| `ProcessedPrefixLearned` | Core invariant transferred by `reachable_refines` |
| `LearnedOnlyDecided` | Core invariant transferred by `reachable_refines` |
| `ProcessedWithinLog` | Core invariant transferred by `reachable_refines` |
| `AppliedPrefixCorrect` | `applied_prefix_correct` |
| `ResponseValidity` | `response_validity`: observed response, selected request, physical execution and dispatch |
| `SeenMatchesDelivered` | `reachable_cache` |
| `RaceWinnerAgreement` | `race_winner_agreement` |
| `NoEarlyDelivery` | `all_safety.noEarlyDelivery`: every delivered item is already in the committed log |

Differences from TLA+ are explicit: arbitrary finite batches (including empty
batches), no `MaxSlots`, no unique-decision scheduling restriction, repeated
learning allowed, and append-only list histories representing set membership.
Explicit re-proposal attempts may repeat an already-buffered item; these would
project to stuttering in the original TLA+ proposal-set abstraction. This added
action lets the model express fair retries by an eventual stable leader.
Selection still happens once globally as in the TLA+ abstraction. A crash only
changes availability/leadership, not retained protocol history. The cache is a
list representation of the seen set; stronger equality with delivered IDs is
proved. Unsafe mutant actions are excluded, not declared correct.

## Liveness: what is assumed and what is proved

Executions are infinite functions from natural-number time to states. `Behavior`
requires the actual initial state and an allowed protocol step at every time.
All of the following are theorem parameters, not new Lean axioms:

1. **Eventually stable live leader** (`StableLeader`): after some finite time,
   one node remains leader and up. Earlier crashes/elections are allowed.
2. **Ingress**: the request eventually has a matching quorum certificate, or an
   allowed timeout certificate. For the paper's quorum-one path this represents
   request forwarding/arrival (L1/L2); the Aegean quorum path additionally needs
   enough matching callers or enabled fallback. Merely submitting a request
   cannot guarantee liveness when no quorum ever forms.
3. **Per-request local/downstream progress** (`RetryProgress`): weak fairness of
   enabled selection, dispatch, response, and actual proposal/re-proposal
   attempts while the request is unagreed. Response progress
   is the downstream-service promise (L3); local stage progress corresponds to
   L4. These contracts name enabling conditions and the immediate effects of
   handlers; they do not assume eventual agreement or delivery.
4. **Stable-leader consensus progress** (`StableConsensusProgress`): every actual
   proposal attempt by the stable leader after stabilization eventually appears
   in the consensus log. Old leaders' buffered proposals need not commit.
5. **Learning and processing** (`DeliveryProgress`): each decided slot eventually
   becomes learned at the target non-faulty replica (CG3 learning); weak fairness
   advances the next slot when it is learned and decided (L4).

`eventually_executed` derives progress through selection, dispatch, and response
using persistence invariants and fairness. `retry_enabled_has_step` proves that
an enabled retry has an actual proposal/re-proposal transition.
`eventually_agreed_stable_consensus` combines retry fairness with the stable
leader's consensus guarantee. `eventually_processed` proves by induction that every
finite agreed prefix is eventually processed. `dedup_covers` proves that an ID
in a processed prefix appears in the delivery history, even if its particular
response was suppressed as a duplicate. `agreed_eventually_delivered` joins
these facts; `eventual_delivery_stable_consensus` connects the entire
ingress-to-delivery chain.

These per-request fairness conditions are intentionally **not** equated with
the existing finite TLA+ configuration's weak fairness over aggregate actions.
With unbounded request domains, fairness of an aggregate action can starve an
individual request indefinitely.

### Why the explicit retry action matters

The PDF's CG3(2) promises agreement for entries proposed by the eventual stable
leader. The older `ConsensusProgress` contract is stronger: it covers all items
already in the global proposal buffer. With re-proposal suppressed, an old
leader's uncommitted item could otherwise remain pending forever.

The expanded model therefore includes `Step.repropose` and records actual
proposal attempts at particular times. The primary theorem requires fair retries
and only the stable leader's own attempts to make consensus progress. It does
not assume progress for every old pending item. The implementation still needs
to satisfy this retry contract; the proof does not mechanically derive runtime
fairness from the paper's informal L1-L4 wording or verify the Go handlers.

### Paper statement correction

In the supplied PDF, section 5.3 states Theorem 2 under CG2-CG3 and L1-L3, while
its proof repeatedly invokes L4. The formal theorem explicitly needs local
execution progress. The paper's statement should include L4; the PDF has not
been edited here.

## Regression and non-vacuity checks

`ProtocolTests.recovery_run` is an explicit reachable execution with leader
failure, a second physical execution returning a different response, conflicting
responses batched in consensus order, and recovery of the old leader. Both
replicas deliver the first committed value once and have matching seen caches.

`physical_execution_can_repeat` disproves once-only physical dispatch in that
reachable failing-leader execution. `fallback_run` checks an explicitly tagged
non-quorum timeout choice. `waiting_behavior` is a valid infinite core behavior
which learns an entry but never processes it; `fairness_is_necessary` proves it
cannot satisfy the delivery progress contract.

`progress_contracts_satisfiable` constructs an infinite behavior extending the
crash/recovery trace and proves that the stable-leader, ingress, local-progress,
consensus-progress, and both replicas' delivery-progress premises hold jointly.
Thus the liveness theorem is not merely passing because its premises are
inconsistent. This witness is a sanity check, not proof that production systems
satisfy those premises.

`retry_contracts_satisfiable` likewise proves the primary stable-consensus and
retry premises jointly satisfiable on an extension of that recovery trace.
`reproposal_reachable` checks an actual retry step from a reachable state.

## Reproduction and remaining boundary

Run `make check-lean`. All imported proofs/tests are compiled with warnings as
errors. `Audit.lean` checks all `Resdet` declarations transitively and permits
only Lean's standard logical axioms (`propext`, `Quot.sound`, `Classical.choice`).
No unfinished proof, native-evaluation trust axiom, or user-added axiom is allowed.

For the current paper-verification goal, consensus internals and Go refinement
are excluded, not unfinished requirements. The in-scope qualifications are the
paper/model correspondence, pending-request retries, and observable delivery
order detailed in `PAPER.md`. This result is not a guarantee of exactly-once
non-idempotent external side effects, which the paper explicitly excludes.
