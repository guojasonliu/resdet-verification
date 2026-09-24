import Resdet.ProposalRetry

/-!
Paper-facing statements for sections 4--6. Consensus is the paper's black-box
contract, not a proof target. Slots here are zero-based (paper index = slot+1).
Liveness uses the explicit pending-request retry contract documented in PAPER.md.
The current paper target excludes recovery: CrashStop.lean restricts this reusable
proof layer to non-rejoining failures. No pseudocode translation is claimed.
-/
namespace Resdet.Paper

section Lists
variable {Request Response : Type} [DecidableEq Request]

/-- Independent first-occurrence lookup in the raw committed sequence. -/
def firstFor (request : Request) : List (Item Request Response) → Option (Item Request Response)
  | [] => none
  | item :: rest => if item.1 = request then some item else firstFor request rest

theorem firstFor_dedupFrom (request : Request) (items : List (Item Request Response))
    (seen : List Request) (fresh : request ∉ seen) :
    firstFor request (dedupFrom seen items) = firstFor request items := by
  induction items generalizing seen with
  | nil => rfl
  | cons item rest ih =>
      by_cases old : item.1 ∈ seen
      · have different : item.1 ≠ request := fun h => fresh (h ▸ old)
        simpa [dedupFrom, old, firstFor, different] using ih seen fresh
      · by_cases same : item.1 = request
        · simp [dedupFrom, firstFor, same, fresh]
        · simp only [dedupFrom, if_neg old, firstFor, if_neg same]
          exact ih (seen ++ [item.1]) (by simp [fresh, Ne.symm same])

theorem firstFor_unique {items : List (Item Request Response)}
    (unique : (items.map Prod.fst).Nodup) {item : Item Request Response}
    (member : item ∈ items) : firstFor item.1 items = some item := by
  induction items with
  | nil => simp at member
  | cons head rest ih =>
      by_cases same : head.1 = item.1
      · have eq := eq_of_same_id unique (List.mem_cons_self) member same
        simp [firstFor, eq]
      · have inside : item ∈ rest := by
          rcases List.mem_cons.mp member with eq | hm
          · exact False.elim (same (congrArg Prod.fst eq.symm))
          · exact hm
        simpa [firstFor, same] using ih (List.nodup_cons.mp unique).2 inside

/-- The incremental batched handler is equivalent to the unbatched ordered scan. -/
def applyBatches (batches : List (List (Item Request Response)))
    (output : List (Item Request Response)) :=
  batches.foldl (fun acc batch => applyItems batch acc) output

theorem batching_equivalent (batches : List (List (Item Request Response)))
    (output : List (Item Request Response)) :
    applyBatches batches output = applyItems batches.flatten output := by
  induction batches generalizing output with
  | nil => rfl
  | cons batch rest ih =>
      simpa [applyBatches, List.flatten_cons, applyItems_append] using
        ih (applyItems batch output)

/-- Regrouping boundaries cannot change delivery, provided flattened order is unchanged. -/
theorem rebatching_preserves_delivery {a b : List (List (Item Request Response))}
    (sameOrder : a.flatten = b.flatten) (output : List (Item Request Response)) :
    applyBatches a output = applyBatches b output := by
  rw [batching_equivalent, batching_equivalent, sameOrder]

end Lists

section Core
variable {Node Request Response : Type} [DecidableEq Node] [DecidableEq Request]

/-- The locally processed slot history, justified by the core induction invariant. -/
def processedLog (s : State Node Request Response) (r : Node) :=
  s.log.take (s.replica r).processed

/-- Paper Lemma 1: both processed histories contain the same learned entry at i. -/
theorem lemma_1_same_processed_entry {s : State Node Request Response} (h : Reachable s)
    (r t : Node) (i : Nat) (hr : i < (s.replica r).processed)
    (ht : i < (s.replica t).processed) :
    ∃ batch, (processedLog s r)[i]? = some batch ∧
      (processedLog s t)[i]? = some batch ∧
      i ∈ (s.replica r).learned ∧ i ∈ (s.replica t).learned := by
  have inv := reachable_invariant h
  have bound : i < s.log.length := Nat.lt_of_lt_of_le hr (inv.processedWithinLog r)
  refine ⟨s.log[i], ?_, ?_, inv.processedPrefixLearned r i hr,
    inv.processedPrefixLearned t i ht⟩
  · simp [processedLog, hr, bound]
  · simp [processedLog, ht, bound]

/-- Paper Lemma 2: processing i means the whole earlier prefix was processed/learned. -/
theorem lemma_2_no_hole_processing {s : State Node Request Response} (h : Reachable s)
    (r : Node) (i : Nat) (hi : i < (s.replica r).processed) :
    ∀ j, j ≤ i → j < (processedLog s r).length ∧ j ∈ (s.replica r).learned := by
  intro j hj
  have inv := reachable_invariant h
  have before : j < (s.replica r).processed := by omega
  exact ⟨by simpa [processedLog, List.length_take, Nat.min_eq_left (inv.processedWithinLog r)]
    using before, inv.processedPrefixLearned r j before⟩

theorem delivery_persists {tr : Nat → State Node Request Response} (b : Behavior tr)
    (r : Node) {a c : Nat} (h : a ≤ c) :
    ((tr a).replica r).delivered <+: ((tr c).replica r).delivered :=
  propagate (p := fun u => ((tr a).replica r).delivered <+: ((tr u).replica r).delivered)
    (fun u hu => hu.trans (step_delivery_monotone (b.next u) r)) h (List.prefix_refl _)

/-- Paper Theorem 1, strengthened to observations at different times. -/
theorem theorem_1_safety {tr : Nat → State Node Request Response} (b : Behavior tr)
    (r t : Node) (a c : Nat) {request : Request} {x y : Response}
    (hx : (request, x) ∈ ((tr a).replica r).delivered)
    (hy : (request, y) ∈ ((tr c).replica t).delivered) : x = y := by
  exact response_agreement (b.reachable (max a c)) r t
    ((delivery_persists b r (Nat.le_max_left _ _)).subset hx)
    ((delivery_persists b t (Nat.le_max_right _ _)).subset hy)

/-- Sections 4.3/6.2: precisely the first committed occurrence, even with conflicting retries. -/
theorem first_committed_response {s : State Node Request Response} (h : Reachable s)
    (r : Node) {request : Request} {value : Response}
    (delivered : (request, value) ∈ (s.replica r).delivered) :
    firstFor request s.log.flatten = some (request, value) := by
  have canonical := firstFor_unique (dedup_nodup s.log.flatten)
    ((delivered_prefix h r).subset delivered)
  have scan := firstFor_dedupFrom request s.log.flatten [] (by simp)
  exact scan.symm.trans canonical

/-- The finite-prefix learning step of the paper's liveness proof. -/
theorem eventually_prefix_learned {tr : Nat → State Node Request Response} (b : Behavior tr)
    (r : Node) (progress : DeliveryProgress tr r) (count start : Nat)
    (decided : count ≤ (tr start).log.length) :
    EventuallyFrom start (fun t => ∀ slot, slot < count → slot ∈ ((tr t).replica r).learned) := by
  induction count with
  | zero => exact ⟨start, Nat.le_refl _, by omega⟩
  | succ k ih =>
      obtain ⟨a, ha, earlier⟩ := ih (by omega)
      obtain ⟨c, hc, last⟩ := progress.learn start k (by omega)
      refine ⟨max a c, by omega, ?_⟩
      intro slot hs
      by_cases eq : slot = k
      · subst slot; exact b.learned_mono r (Nat.le_max_right _ _) last
      · exact b.learned_mono r (Nat.le_max_left _ _) (earlier slot (by omega))

/-- Equal delivered prefixes produce equal application states for a deterministic
continuation from a common initial state. Not a theorem about arbitrary schedulers. -/
theorem deterministic_continuation {App : Type} {s : State Node Request Response}
    (h : Reachable s) (r t : Node) (count : Nat)
    (hr : count ≤ (s.replica r).delivered.length)
    (ht : count ≤ (s.replica t).delivered.length)
    (initialApp : App) (advance : App → Item Request Response → App) :
    ((s.replica r).delivered.take count).foldl advance initialApp =
      ((s.replica t).delivered.take count).foldl advance initialApp := by
  have equal : (s.replica r).delivered.take count = (s.replica t).delivered.take count := by
    rcases prefix_agreement h r t with ⟨suffix, eq⟩ | ⟨suffix, eq⟩
    · rw [← eq, List.take_append_of_le_length hr]
    · rw [← eq, List.take_append_of_le_length ht]
  rw [equal]

/-- Section 3's race example, restricted to any common set of competing calls.
The consuming application must actually use delivery order as its race order. -/
theorem race_winner_for_group {s : State Node Request Response} (h : Reachable s)
    (r t : Node) (eligible : Request → Bool) {x y : Item Request Response}
    (hx : ((s.replica r).delivered.filter (fun item => eligible item.1)).head? = some x)
    (hy : ((s.replica t).delivered.filter (fun item => eligible item.1)).head? = some y) : x = y := by
  rcases prefix_agreement h r t with pre | pre
  · exact heads_eq_of_prefix (pre.filter (fun item => eligible item.1)) hx hy
  · exact (heads_eq_of_prefix (pre.filter (fun item => eligible item.1)) hy hx).symm

end Core

section Protocol
variable {Node Request Payload Response : Type} [DecidableEq Node] [DecidableEq Request]

/-- The paper only needs handler progress for requests not yet agreed. In
particular, this does not demand another physical execution of a completed call. -/
structure PendingHandlers (cfg : Protocol.Config)
    (tr : Nat → Protocol.State Node Request Payload Response) (n : Node) (request : Request) : Prop where
  select : WeakFair (fun t => Protocol.SelectEnabled cfg (tr t) n request ∧
    ¬ Protocol.Agreed (tr t) request) (fun t => Protocol.Selected (tr (t+1)) request)
  dispatch : WeakFair (fun t => Protocol.DispatchEnabled cfg (tr t) n request ∧
    ¬ Protocol.Agreed (tr t) request) (fun t => Protocol.Dispatched (tr (t+1)) n request)
  respond : WeakFair (fun t => Protocol.RespondEnabled (tr t) n request ∧
    ¬ Protocol.Agreed (tr t) request) (fun t => Protocol.Executed (tr (t+1)) n request)
  repropose : WeakFair (fun t => Protocol.RetryEnabled (tr t) n request)
    (fun t => ∃ value, Protocol.ProposalAttempt tr t n (request, value))

omit [DecidableEq Node] [DecidableEq Request] in
theorem PendingHandlers.ofRetry {cfg : Protocol.Config}
    {tr : Nat → Protocol.State Node Request Payload Response} {n : Node} {request : Request}
    (h : Protocol.RetryProgress cfg tr n request) : PendingHandlers cfg tr n request := by
  refine ⟨?_, ?_, ?_, h.repropose⟩
  · intro start enabled; exact h.select start (fun t ht => (enabled t ht).1)
  · intro start enabled; exact h.dispatch start (fun t ht => (enabled t ht).1)
  · intro start enabled; exact h.respond start (fun t ht => (enabled t ht).1)

omit [DecidableEq Node] [DecidableEq Request] in
theorem pending_fairness {enabled occurs pending : Nat → Prop} {start : Nat}
    (neverDone : ∀ t, start ≤ t → pending t)
    (fair : WeakFair (fun t => enabled t ∧ pending t) occurs) : WeakFair enabled occurs := by
  intro a continuous
  obtain ⟨t, ht, event⟩ := fair (max a start) (by
    intro u hu
    exact ⟨continuous u (by omega), neverDone u (by omega)⟩)
  exact ⟨t, by omega, event⟩

/-- Step (1) of Theorem 2, with fairness required only while the request is pending. -/
theorem eventually_agreed {cfg : Protocol.Config} {leader n : Node}
    {tr : Nat → Protocol.State Node Request Payload Response}
    (b : Protocol.Behavior cfg leader tr) (start : Nat)
    (stable : Protocol.StableLeader tr n start) (request : Request)
    (ready : Protocol.GateReady cfg (tr start) request)
    (handlers : PendingHandlers cfg tr n request)
    (consensus : Protocol.StableConsensusProgress tr n start) :
    EventuallyFrom start (fun t => Protocol.Agreed (tr t) request) := by
  classical
  apply Classical.byContradiction
  intro never
  have stillPending : ∀ t, start ≤ t → ¬ Protocol.Agreed (tr t) request :=
    fun t ht agreed => never ⟨t, ht, agreed⟩
  have progress : Protocol.RetryProgress cfg tr n request :=
    ⟨pending_fairness stillPending handlers.select,
      pending_fairness stillPending handlers.dispatch,
      pending_fairness stillPending handlers.respond, handlers.repropose⟩
  exact never (Protocol.eventually_agreed_stable_consensus b start stable request ready
    progress consensus)

theorem eventually_delivered {cfg : Protocol.Config} {leader n : Node}
    {tr : Nat → Protocol.State Node Request Payload Response}
    (b : Protocol.Behavior cfg leader tr) (stabilizes : Nat)
    (stable : Protocol.StableLeader tr n stabilizes) (request : Request)
    (ingress : EventuallyFrom 0 (fun t => Protocol.GateReady cfg (tr t) request))
    (handlers : PendingHandlers cfg tr n request)
    (consensus : Protocol.StableConsensusProgress tr n stabilizes)
    (r : Node) (delivery : DeliveryProgress (fun t => (tr t).core) r) :
    EventuallyFrom 0 (fun t => ∃ value, (request, value) ∈ ((tr t).core.replica r).delivered) := by
  obtain ⟨received, _, ready⟩ := ingress
  let start := max stabilizes received
  have readyNow : Protocol.GateReady cfg (tr start) request :=
    propagate (fun t ht => Protocol.gate_step_mono (b.next t) ht) (Nat.le_max_right _ _) ready
  have stableNow : Protocol.StableLeader tr n start :=
    fun t ht => stable t (Nat.le_trans (Nat.le_max_left _ _) ht)
  have consensusNow : Protocol.StableConsensusProgress tr n start :=
    fun t ht => consensus t (Nat.le_trans (Nat.le_max_left _ _) ht)
  obtain ⟨d, _, agreed⟩ := eventually_agreed b start stableNow request readyNow handlers consensusNow
  obtain ⟨t, _, delivered⟩ := agreed_eventually_delivered b.core r delivery d agreed
  exact ⟨t, Nat.zero_le _, delivered⟩

omit [DecidableEq Node] [DecidableEq Request] in
/-- The paper's core Resdet path has no Aegean quorum gate: one arrival suffices. -/
theorem single_arrival_ready {cfg : Protocol.Config} (quorumOne : cfg.quorum = 1)
    {s : Protocol.State Node Request Payload Response} {sender : Node}
    {request : Request} {payload : Payload} (arrival : (sender, request, payload) ∈ s.ballots) :
    Protocol.GateReady cfg s request := by
  refine ⟨payload, false, ?_, by simp⟩
  exact ⟨[sender], by simp, by simp [quorumOne], by simpa using arrival⟩

omit [DecidableEq Node] [DecidableEq Request] in
/-- Section 6.1's enabled force-yield path needs one arrival, not a matching quorum.
The correctness of the selected payload is deliberately not asserted. -/
theorem fallback_arrival_ready {cfg : Protocol.Config} (fallback : cfg.timeoutFallback = true)
    {s : Protocol.State Node Request Payload Response} {sender : Node}
    {request : Request} {payload : Payload} (arrival : (sender, request, payload) ∈ s.ballots) :
    Protocol.GateReady cfg s request :=
  ⟨payload, true, ⟨sender, arrival⟩, fun _ => fallback⟩

/-- Paper Theorem 2 at the protocol abstraction boundary, for every submitted
request and non-faulty replica. L1/L2 are represented by eventual arrival;
L3/L4 plus pending-request retries are represented by PendingHandlers and
DeliveryProgress. CrashStop.lean specializes this general result to the author's
no-recovery scope. The result is stronger than one delivery: it remains exactly one. -/
theorem theorem_2_liveness {cfg : Protocol.Config} {leader n : Node}
    {tr : Nat → Protocol.State Node Request Payload Response}
    (b : Protocol.Behavior cfg leader tr) (quorumOne : cfg.quorum = 1)
    (submitted : Request → Prop) (nonfaulty : Node → Prop)
    (stabilizes : Nat) (stable : Protocol.StableLeader tr n stabilizes)
    (ingress : ∀ request, submitted request → EventuallyFrom 0
      (fun t => ∃ sender payload, (sender, request, payload) ∈ (tr t).ballots))
    (handlers : ∀ request, submitted request → PendingHandlers cfg tr n request)
    (consensus : Protocol.StableConsensusProgress tr n stabilizes)
    (replicas : ∀ r, nonfaulty r → DeliveryProgress (fun t => (tr t).core) r) :
    ∀ request, submitted request → ∀ r, nonfaulty r →
      ∃ time value, ∀ later, time ≤ later →
        (request, value) ∈ ((tr later).core.replica r).delivered ∧
        (((tr later).core.replica r).delivered.map Prod.fst).count request = 1 := by
  intro request hs r hr
  obtain ⟨arrival, ha, sender, payload, received⟩ := ingress request hs
  have ready : EventuallyFrom 0 (fun t => Protocol.GateReady cfg (tr t) request) :=
    ⟨arrival, ha, single_arrival_ready quorumOne received⟩
  obtain ⟨time, _, value, delivered⟩ := eventually_delivered b
    stabilizes stable request ready (handlers request hs) consensus r (replicas r hr)
  refine ⟨time, value, ?_⟩
  intro later hl
  have member := (delivery_persists b.core r hl).subset delivered
  have idMember : request ∈ ((tr later).core.replica r).delivered.map Prod.fst :=
    List.mem_map_of_mem member
  have positive := List.count_pos_iff.mpr idMember
  have bound := delivery_count_le_one (b.core.reachable later) r request
  exact ⟨member, by omega⟩

end Protocol
end Resdet.Paper
