------------------------------ MODULE Resdet ------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************
Resdet/EO model

This module models the protocol above a total-order consensus abstraction.
Consensus safety itself is assumed: DecideOne/DecidePair append to one global,
immutable log. The model focuses on the Resdet-specific obligations around
caller quorum selection, leader-only dispatch, nondeterministic external
responses, ordered learning, batching, and duplicate suppression.

The Mutant* constants deliberately weaken individual rules. Their configs
are expected to produce TLC counterexamples and act as regression tests for
the invariants.

SubmitVote and Quorum generalize two request-ingress modes. Quorum = 1 models
the paper's handle_request/forward path, where one invocation reaching the
leader is enough. Quorum = 2 models the matching 2-of-3 caller gate used by
the Aegean integration in aegean-clone.
***************************************************************************)

CONSTANTS
    Replicas,
    RequestIds,
    Payloads,
    Responses,
    NoNode,
    NoValue,
    Quorum,
    MaxSlots,
    EnableBatching,
    PrioritizeUniqueDecisions,
    EnableTimeoutFallback,
    EnableNoLeaderFallback,
    EnableCrashes,
    MutantNoDedup,
    MutantNonContiguous,
    MutantAllDispatch,
    MutantNoQuorum,
    MutantEarlyDelivery

ASSUME
    /\ Replicas # {}
    /\ RequestIds # {}
    /\ Payloads # {}
    /\ Responses # {}
    /\ Quorum \in 1..Cardinality(Replicas)
    /\ MaxSlots \in Nat \ {0}
    /\ NoNode \notin Replicas
    /\ NoValue \notin (Payloads \union Responses)
    /\ EnableBatching \in BOOLEAN
    /\ PrioritizeUniqueDecisions \in BOOLEAN
    /\ EnableTimeoutFallback \in BOOLEAN
    /\ EnableNoLeaderFallback \in BOOLEAN
    /\ EnableCrashes \in BOOLEAN
    /\ MutantNoDedup \in BOOLEAN
    /\ MutantNonContiguous \in BOOLEAN
    /\ MutantAllDispatch \in BOOLEAN
    /\ MutantNoQuorum \in BOOLEAN
    /\ MutantEarlyDelivery \in BOOLEAN

ResponseItems == [rid : RequestIds, value : Responses]

SingleBatches == {<<item>> : item \in ResponseItems}

DoubleBatches ==
    {<<first, second>> :
        first \in ResponseItems,
        second \in ResponseItems}

BatchType ==
    IF EnableBatching
    THEN SingleBatches \union DoubleBatches
    ELSE SingleBatches

VARIABLES
    leader,
    up,
    votes,
    selected,
    selectedByFallback,
    dispatchers,
    execResponse,
    observed,
    proposed,
    consensusLog,
    learned,
    processed,
    delivered,
    seen,
    unauthorizedDispatch,
    earlyDelivery

vars ==
    <<leader, up, votes, selected, selectedByFallback, dispatchers,
      execResponse, observed, proposed, consensusLog, learned, processed,
      delivered, seen, unauthorizedDispatch, earlyDelivery>>

Symmetry == Permutations(Replicas)

HasVoted(replica, request) ==
    \E payload \in Payloads : replica \in votes[request][payload]

ObservedItem(request, responseValue) ==
    [rid |-> request, value |-> responseValue]

RECURSIVE FlattenBatches(_)
FlattenBatches(batches) ==
    IF Len(batches) = 0
    THEN <<>>
    ELSE Head(batches) \o FlattenBatches(Tail(batches))

DecidedRequestIds ==
    LET items == FlattenBatches(consensusLog)
    IN {items[index].rid : index \in 1..Len(items)}

ConsensusItems ==
    LET items == FlattenBatches(consensusLog)
    IN {items[index] : index \in 1..Len(items)}

UndecidedProposals ==
    {item \in proposed : item.rid \notin DecidedRequestIds}

(***************************************************************************
Prefer a proposal for an as-yet undecided request. Once every modeled
request has a log position, retries may append duplicates. This avoids a
bounded log being filled by retries before another request can be decided,
while still exercising duplicate slots and duplicate items within a batch.
***************************************************************************)
EligibleProposalItems ==
    IF PrioritizeUniqueDecisions
    THEN
        IF UndecidedProposals # {}
        THEN UndecidedProposals
        ELSE IF DecidedRequestIds = RequestIds THEN proposed ELSE {}
    ELSE proposed

RECURSIVE ApplyItems(_, _, _)
ApplyItems(items, alreadySeen, output) ==
    IF Len(items) = 0
    THEN [seen |-> alreadySeen, output |-> output]
    ELSE
        LET item == Head(items)
            shouldApply == MutantNoDedup \/ item.rid \notin alreadySeen
            nextSeen ==
                IF shouldApply
                THEN alreadySeen \union {item.rid}
                ELSE alreadySeen
            nextOutput ==
                IF shouldApply
                THEN Append(output, item)
                ELSE output
        IN ApplyItems(Tail(items), nextSeen, nextOutput)

RECURSIVE DedupFrom(_, _)
DedupFrom(items, alreadySeen) ==
    IF Len(items) = 0
    THEN <<>>
    ELSE
        LET item == Head(items)
        IN IF item.rid \in alreadySeen
           THEN DedupFrom(Tail(items), alreadySeen)
           ELSE <<item>> \o DedupFrom(
                                Tail(items),
                                alreadySeen \union {item.rid})

FlattenedPrefix(index) ==
    IF index = 0
    THEN <<>>
    ELSE FlattenBatches(SubSeq(consensusLog, 1, index))

CorrectAppliedPrefix(replica) ==
    DedupFrom(FlattenedPrefix(processed[replica]), {})

IsPrefix(left, right) ==
    \/ left = <<>>
    \/ /\ Len(left) <= Len(right)
       /\ SubSeq(right, 1, Len(left)) = left

DeliveredPositions(replica, request) ==
    {index \in 1..Len(delivered[replica]) :
        delivered[replica][index].rid = request}

DeliveredValues(replica, request) ==
    {delivered[replica][index].value :
        index \in DeliveredPositions(replica, request)}

RaceWinner(replica) ==
    IF Len(delivered[replica]) = 0
    THEN NoValue
    ELSE Head(delivered[replica]).rid

Init ==
    /\ leader \in Replicas
    /\ up = Replicas
    /\ votes = [request \in RequestIds |->
                    [payload \in Payloads |-> {}]]
    /\ selected = [request \in RequestIds |-> NoValue]
    /\ selectedByFallback = {}
    /\ dispatchers = [request \in RequestIds |-> {}]
    /\ execResponse = [request \in RequestIds |->
                           [replica \in Replicas |-> NoValue]]
    /\ observed = {}
    /\ proposed = {}
    /\ consensusLog = <<>>
    /\ learned = [replica \in Replicas |-> {}]
    /\ processed = [replica \in Replicas |-> 0]
    /\ delivered = [replica \in Replicas |-> <<>>]
    /\ seen = [replica \in Replicas |-> {}]
    /\ unauthorizedDispatch = FALSE
    /\ earlyDelivery = FALSE

SubmitVote(replica, request, payload) ==
    /\ replica \in up
    /\ ~HasVoted(replica, request)
    /\ votes' = [votes EXCEPT
                    ![request][payload] = @ \union {replica}]
    /\ UNCHANGED
        <<leader, up, selected, selectedByFallback, dispatchers,
          execResponse, observed, proposed, consensusLog, learned, processed,
          delivered, seen, unauthorizedDispatch, earlyDelivery>>

SelectByQuorum(replica, request, payload) ==
    LET required == IF MutantNoQuorum THEN 1 ELSE Quorum
    IN
    /\ replica = leader
    /\ replica \in up
    /\ selected[request] = NoValue
    /\ Cardinality(votes[request][payload]) >= required
    /\ selected' = [selected EXCEPT ![request] = payload]
    /\ UNCHANGED
        <<leader, up, votes, selectedByFallback, dispatchers,
          execResponse, observed, proposed, consensusLog, learned, processed,
          delivered, seen, unauthorizedDispatch, earlyDelivery>>

TimeoutSelect(replica, request, payload) ==
    /\ EnableTimeoutFallback
    /\ replica = leader
    /\ replica \in up
    /\ selected[request] = NoValue
    /\ votes[request][payload] # {}
    /\ selected' = [selected EXCEPT ![request] = payload]
    /\ selectedByFallback' = selectedByFallback \union {request}
    /\ UNCHANGED
        <<leader, up, votes, dispatchers, execResponse, observed, proposed,
          consensusLog, learned, processed, delivered, seen,
          unauthorizedDispatch, earlyDelivery>>

Dispatch(replica, request) ==
    /\ selected[request] # NoValue
    /\ replica \in up
    /\ IF MutantAllDispatch THEN TRUE ELSE replica = leader
    /\ replica \notin dispatchers[request]
    /\ MutantAllDispatch \/ EnableCrashes \/ dispatchers[request] = {}
    /\ dispatchers' = [dispatchers EXCEPT
                         ![request] = @ \union {replica}]
    /\ unauthorizedDispatch' =
        (unauthorizedDispatch \/ (replica # leader))
    /\ UNCHANGED
        <<leader, up, votes, selected, selectedByFallback, execResponse,
          observed, proposed, consensusLog, learned, processed, delivered,
          seen, earlyDelivery>>

ExternalRespond(replica, request, responseValue) ==
    /\ replica \in dispatchers[request]
    /\ execResponse[request][replica] = NoValue
    /\ execResponse' = [execResponse EXCEPT
                          ![request][replica] = responseValue]
    /\ observed' =
        observed \union {ObservedItem(request, responseValue)}
    /\ UNCHANGED
        <<leader, up, votes, selected, selectedByFallback, dispatchers,
          proposed, consensusLog, learned, processed, delivered, seen,
          unauthorizedDispatch, earlyDelivery>>

ProposeResponse(replica, request, responseValue) ==
    LET item == ObservedItem(request, responseValue)
    IN
    /\ replica = leader
    /\ replica \in up
    /\ replica \in dispatchers[request]
    /\ execResponse[request][replica] = responseValue
    /\ item \notin proposed
    /\ proposed' = proposed \union {item}
    /\ UNCHANGED
        <<leader, up, votes, selected, selectedByFallback, dispatchers,
          execResponse, observed, consensusLog, learned, processed,
          delivered, seen, unauthorizedDispatch, earlyDelivery>>

DecideOne(item) ==
    /\ Len(consensusLog) < MaxSlots
    /\ item \in EligibleProposalItems
    /\ consensusLog' = Append(consensusLog, <<item>>)
    /\ UNCHANGED
        <<leader, up, votes, selected, selectedByFallback, dispatchers,
          execResponse, observed, proposed, learned, processed, delivered,
          seen, unauthorizedDispatch, earlyDelivery>>

DecidePair(first, second) ==
    /\ EnableBatching
    /\ Len(consensusLog) < MaxSlots
    /\ first \in EligibleProposalItems
    /\ second \in proposed
    /\ consensusLog' = Append(consensusLog, <<first, second>>)
    /\ UNCHANGED
        <<leader, up, votes, selected, selectedByFallback, dispatchers,
          execResponse, observed, proposed, learned, processed, delivered,
          seen, unauthorizedDispatch, earlyDelivery>>

LearnSlot(replica, slot) ==
    /\ replica \in up
    /\ slot \in 1..Len(consensusLog)
    /\ slot \notin learned[replica]
    /\ learned' = [learned EXCEPT ![replica] = @ \union {slot}]
    /\ UNCHANGED
        <<leader, up, votes, selected, selectedByFallback, dispatchers,
          execResponse, observed, proposed, consensusLog, processed,
          delivered, seen, unauthorizedDispatch, earlyDelivery>>

ProcessContiguous(replica) ==
    LET slot == processed[replica] + 1
        result ==
            ApplyItems(
                consensusLog[slot],
                seen[replica],
                delivered[replica])
    IN
    /\ replica \in up
    /\ slot \in 1..Len(consensusLog)
    /\ slot \in learned[replica]
    /\ processed' = [processed EXCEPT ![replica] = slot]
    /\ seen' = [seen EXCEPT ![replica] = result.seen]
    /\ delivered' = [delivered EXCEPT ![replica] = result.output]
    /\ UNCHANGED
        <<leader, up, votes, selected, selectedByFallback, dispatchers,
          execResponse, observed, proposed, consensusLog, learned,
          unauthorizedDispatch, earlyDelivery>>

ProcessNonContiguous(replica, slot) ==
    LET result ==
            ApplyItems(
                consensusLog[slot],
                seen[replica],
                delivered[replica])
    IN
    /\ MutantNonContiguous
    /\ replica \in up
    /\ slot \in learned[replica]
    /\ slot > processed[replica] + 1
    /\ processed' = [processed EXCEPT ![replica] = slot]
    /\ seen' = [seen EXCEPT ![replica] = result.seen]
    /\ delivered' = [delivered EXCEPT ![replica] = result.output]
    /\ UNCHANGED
        <<leader, up, votes, selected, selectedByFallback, dispatchers,
          execResponse, observed, proposed, consensusLog, learned,
          unauthorizedDispatch, earlyDelivery>>

DeliverBeforeConsensus(replica, item) ==
    /\ MutantEarlyDelivery
    /\ replica \in up
    /\ item \in observed
    /\ item.rid \notin seen[replica]
    /\ delivered' = [delivered EXCEPT
                       ![replica] = Append(@, item)]
    /\ seen' = [seen EXCEPT
                  ![replica] = @ \union {item.rid}]
    /\ earlyDelivery' = TRUE
    /\ UNCHANGED
        <<leader, up, votes, selected, selectedByFallback, dispatchers,
          execResponse, observed, proposed, consensusLog, learned, processed,
          unauthorizedDispatch>>

Crash(replica) ==
    /\ EnableCrashes
    /\ replica \in up
    /\ up' = up \ {replica}
    /\ leader' = IF leader = replica THEN NoNode ELSE leader
    /\ UNCHANGED
        <<votes, selected, selectedByFallback, dispatchers, execResponse,
          observed, proposed, consensusLog, learned, processed, delivered,
          seen, unauthorizedDispatch, earlyDelivery>>

Recover(replica) ==
    /\ EnableCrashes
    /\ replica \in Replicas \ up
    /\ up' = up \union {replica}
    /\ UNCHANGED
        <<leader, votes, selected, selectedByFallback, dispatchers,
          execResponse, observed, proposed, consensusLog, learned, processed,
          delivered, seen, unauthorizedDispatch, earlyDelivery>>

Elect(replica) ==
    /\ EnableCrashes
    /\ leader = NoNode
    /\ replica \in up
    /\ leader' = replica
    /\ UNCHANGED
        <<up, votes, selected, selectedByFallback, dispatchers, execResponse,
          observed, proposed, consensusLog, learned, processed, delivered,
          seen, unauthorizedDispatch, earlyDelivery>>

(***************************************************************************
The implementation's no-known-leader path sends directly. These two actions
model that escape hatch separately from strict Resdet. They intentionally
bypass consensus and are used only by a boundary/counterexample config.
***************************************************************************)
NoLeaderDispatch(replica, request, payload) ==
    /\ EnableNoLeaderFallback
    /\ leader = NoNode
    /\ replica \in up
    /\ replica \in votes[request][payload]
    /\ selected[request] \in {NoValue, payload}
    /\ replica \notin dispatchers[request]
    /\ selected' = [selected EXCEPT ![request] = payload]
    /\ selectedByFallback' =
        selectedByFallback \union {request}
    /\ dispatchers' = [dispatchers EXCEPT
                         ![request] = @ \union {replica}]
    /\ unauthorizedDispatch' = TRUE
    /\ UNCHANGED
        <<leader, up, votes, execResponse, observed, proposed, consensusLog,
          learned, processed, delivered, seen, earlyDelivery>>

DirectNoLeaderRespond(replica, request, responseValue) ==
    LET item == ObservedItem(request, responseValue)
    IN
    /\ EnableNoLeaderFallback
    /\ leader = NoNode
    /\ replica \in up
    /\ replica \in dispatchers[request]
    /\ execResponse[request][replica] = NoValue
    /\ request \notin seen[replica]
    /\ execResponse' = [execResponse EXCEPT
                          ![request][replica] = responseValue]
    /\ observed' = observed \union {item}
    /\ delivered' = [delivered EXCEPT
                       ![replica] = Append(@, item)]
    /\ seen' = [seen EXCEPT
                  ![replica] = @ \union {request}]
    /\ earlyDelivery' = TRUE
    /\ UNCHANGED
        <<leader, up, votes, selected, selectedByFallback, dispatchers,
          proposed, consensusLog, learned, processed, unauthorizedDispatch>>

SubmitVoteAction ==
    \E replica \in Replicas,
       request \in RequestIds,
       payload \in Payloads :
        SubmitVote(replica, request, payload)

SelectAction ==
    \/ \E replica \in Replicas,
          request \in RequestIds,
          payload \in Payloads :
          SelectByQuorum(replica, request, payload)
    \/ \E replica \in Replicas,
          request \in RequestIds,
          payload \in Payloads :
          TimeoutSelect(replica, request, payload)

DispatchAction ==
    \E replica \in Replicas, request \in RequestIds :
        Dispatch(replica, request)

ExternalRespondAction ==
    \E replica \in Replicas,
       request \in RequestIds,
       responseValue \in Responses :
        ExternalRespond(replica, request, responseValue)

ProposeResponseAction ==
    \E replica \in Replicas,
       request \in RequestIds,
       responseValue \in Responses :
        ProposeResponse(replica, request, responseValue)

DecideAction ==
    \/ \E item \in ResponseItems : DecideOne(item)
    \/ \E first \in ResponseItems, second \in ResponseItems :
          DecidePair(first, second)

LearnAction ==
    \E replica \in Replicas, slot \in 1..MaxSlots :
        LearnSlot(replica, slot)

ProcessAction ==
    \E replica \in Replicas : ProcessContiguous(replica)

Next ==
    \/ SubmitVoteAction
    \/ SelectAction
    \/ DispatchAction
    \/ ExternalRespondAction
    \/ ProposeResponseAction
    \/ DecideAction
    \/ LearnAction
    \/ ProcessAction
    \/ \E replica \in Replicas, slot \in 1..MaxSlots :
          ProcessNonContiguous(replica, slot)
    \/ \E replica \in Replicas, item \in ResponseItems :
          DeliverBeforeConsensus(replica, item)
    \/ \E replica \in Replicas : Crash(replica)
    \/ \E replica \in Replicas : Recover(replica)
    \/ \E replica \in Replicas : Elect(replica)
    \/ \E replica \in Replicas,
          request \in RequestIds,
          payload \in Payloads :
          NoLeaderDispatch(replica, request, payload)
    \/ \E replica \in Replicas,
          request \in RequestIds,
          responseValue \in Responses :
          DirectNoLeaderRespond(replica, request, responseValue)

Spec == Init /\ [][Next]_vars

FairSpec ==
    Spec
    /\ WF_vars(SubmitVoteAction)
    /\ WF_vars(SelectAction)
    /\ WF_vars(DispatchAction)
    /\ WF_vars(ExternalRespondAction)
    /\ WF_vars(ProposeResponseAction)
    /\ WF_vars(DecideAction)
    /\ WF_vars(LearnAction)
    /\ WF_vars(ProcessAction)

(***************************************************************************
Safety invariants
***************************************************************************)
TypeOK ==
    /\ leader \in Replicas \union {NoNode}
    /\ up \subseteq Replicas
    /\ votes \in [RequestIds -> [Payloads -> SUBSET Replicas]]
    /\ selected \in [RequestIds -> Payloads \union {NoValue}]
    /\ selectedByFallback \subseteq RequestIds
    /\ dispatchers \in [RequestIds -> SUBSET Replicas]
    /\ execResponse \in
        [RequestIds -> [Replicas -> Responses \union {NoValue}]]
    /\ observed \subseteq ResponseItems
    /\ proposed \subseteq ResponseItems
    /\ consensusLog \in Seq(BatchType)
    /\ Len(consensusLog) <= MaxSlots
    /\ learned \in [Replicas -> SUBSET (1..MaxSlots)]
    /\ processed \in [Replicas -> 0..MaxSlots]
    /\ delivered \in [Replicas -> Seq(ResponseItems)]
    /\ seen \in [Replicas -> SUBSET RequestIds]
    /\ unauthorizedDispatch \in BOOLEAN
    /\ earlyDelivery \in BOOLEAN

SelectionJustified ==
    \A request \in RequestIds :
        selected[request] # NoValue =>
            IF request \in selectedByFallback
            THEN Cardinality(votes[request][selected[request]]) >= 1
            ELSE Cardinality(votes[request][selected[request]]) >= Quorum

StrictQuorumOnly == selectedByFallback = {}

NoDispatchBeforeSelection ==
    \A request \in RequestIds :
        dispatchers[request] # {} => selected[request] # NoValue

OnlyAuthorizedDispatch == ~unauthorizedDispatch

ObservedHasPhysicalExecution ==
    \A item \in observed :
        \E replica \in dispatchers[item.rid] :
            execResponse[item.rid][replica] = item.value

ProposalValidity == proposed \subseteq observed

ConsensusValidity == ConsensusItems \subseteq proposed

AtMostOnePhysicalDispatch ==
    \A request \in RequestIds :
        Cardinality(dispatchers[request]) <= 1

AtMostOnceDelivery ==
    \A replica \in Replicas, request \in RequestIds :
        Cardinality(DeliveredPositions(replica, request)) <= 1

ResponseAgreement ==
    \A left \in Replicas,
       right \in Replicas,
       request \in RequestIds :
        /\ DeliveredValues(left, request) # {}
        /\ DeliveredValues(right, request) # {}
        => DeliveredValues(left, request) =
           DeliveredValues(right, request)

PrefixAgreement ==
    \A left \in Replicas, right \in Replicas :
        IsPrefix(delivered[left], delivered[right])
        \/ IsPrefix(delivered[right], delivered[left])

ProcessedPrefixLearned ==
    \A replica \in Replicas :
        (1..processed[replica]) \subseteq learned[replica]

LearnedOnlyDecided ==
    \A replica \in Replicas :
        learned[replica] \subseteq 1..Len(consensusLog)

ProcessedWithinLog ==
    \A replica \in Replicas :
        processed[replica] <= Len(consensusLog)

AppliedPrefixCorrect ==
    \A replica \in Replicas :
        delivered[replica] = CorrectAppliedPrefix(replica)

ResponseValidity ==
    \A replica \in Replicas :
        \A index \in 1..Len(delivered[replica]) :
            LET item == delivered[replica][index]
            IN /\ item \in observed
               /\ selected[item.rid] # NoValue

SeenMatchesDelivered ==
    \A replica \in Replicas :
        seen[replica] =
            {delivered[replica][index].rid :
                index \in 1..Len(delivered[replica])}

RaceWinnerAgreement ==
    \A left \in Replicas, right \in Replicas :
        /\ RaceWinner(left) # NoValue
        /\ RaceWinner(right) # NoValue
        => RaceWinner(left) = RaceWinner(right)

NoEarlyDelivery == ~earlyDelivery

(***************************************************************************
Liveness is checked only in the stable-leader configuration. With a finite
request set and fair actions, every request should reach every replica.
***************************************************************************)
Completion ==
    <>(\A replica \in Replicas : seen[replica] = RequestIds)

=============================================================================
