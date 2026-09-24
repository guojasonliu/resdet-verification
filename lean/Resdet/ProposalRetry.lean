import Resdet.ProtocolLiveness

/-!
Liveness with CG3 restricted to proposal attempts by the stable leader.
Unlike the global-buffer theorem, this does not demand that an old leader's
uncommitted proposal be committed. A fair re-proposal action is explicit.
-/
namespace Resdet.Protocol

variable {Node Request Payload Response : Type}
variable [DecidableEq Node] [DecidableEq Request]

def Agreed (s : State Node Request Payload Response) (request : Request) :=
  request ∈ s.core.log.flatten.map Prod.fst

def ProposalAttempt (tr : Nat → State Node Request Payload Response) (t : Nat)
    (n : Node) (item : Item Request Response) :=
  (tr t).leader = some n ∧ (n, item.1, item.2) ∈ (tr t).executions ∧
    (tr (t+1)).proposed = item :: (tr t).proposed

def RetryEnabled (s : State Node Request Payload Response) (n : Node) (request : Request) :=
  s.leader = some n ∧ s.up n = true ∧ Executed s n request ∧ ¬ Agreed s request

/-- CG3(2) only for actual attempts by the stable leader after stabilization. -/
def StableConsensusProgress (tr : Nat → State Node Request Payload Response)
    (n : Node) (stabilizes : Nat) :=
  ∀ t, stabilizes ≤ t → ∀ item, ProposalAttempt tr t n item →
    EventuallyFrom t (fun u => item ∈ (tr u).core.log.flatten)

/-- L3/L4 action-level progress including retries while a request is uncommitted.
No field assumes that consensus agrees or that any replica delivers. -/
structure RetryProgress (cfg : Config) (tr : Nat → State Node Request Payload Response)
    (n : Node) (request : Request) : Prop where
  select : WeakFair (fun t => SelectEnabled cfg (tr t) n request)
    (fun t => Selected (tr (t+1)) request)
  dispatch : WeakFair (fun t => DispatchEnabled cfg (tr t) n request)
    (fun t => Dispatched (tr (t+1)) n request)
  respond : WeakFair (fun t => RespondEnabled (tr t) n request)
    (fun t => Executed (tr (t+1)) n request)
  repropose : WeakFair (fun t => RetryEnabled (tr t) n request)
    (fun t => ∃ value, ProposalAttempt tr t n (request, value))

/-- Retry fairness is not imposed on an impossible action: its guard always
admits a real propose/repropose transition, without assuming a safety result. -/
theorem retry_enabled_has_step {cfg : Config} {s : State Node Request Payload Response}
    {n : Node} {request : Request} (h : RetryEnabled s n request) :
    ∃ value t, Step cfg s t ∧ t.proposed = (request, value) :: s.proposed := by
  classical
  obtain ⟨hl, hu, ⟨value, executed⟩, _⟩ := h
  refine ⟨value, { s with proposed := (request, value) :: s.proposed }, ?_, rfl⟩
  by_cases buffered : (request, value) ∈ s.proposed
  · exact .repropose s n request value hl hu executed buffered
  · exact .propose s n request value hl hu executed buffered

theorem agreed_implies_proposed {cfg : Config} {leader : Node}
    {s : State Node Request Payload Response} (h : Reachable cfg leader s)
    {request : Request} (ha : Agreed s request) : Proposed s request := by
  obtain ⟨⟨id, value⟩, hm, hid⟩ := List.mem_map.mp ha
  change id = request at hid
  subst id
  exact ⟨value, consensus_validity h hm⟩

theorem RetryProgress.localProgress {cfg : Config} {leader n : Node}
    {tr : Nat → State Node Request Payload Response} (b : Behavior cfg leader tr)
    {request : Request} (p : RetryProgress cfg tr n request) : LocalProgress cfg tr n request := by
  refine ⟨p.select, p.dispatch, p.respond, ?_⟩
  intro start enabled
  have retry : ∀ t, start ≤ t → RetryEnabled (tr t) n request := by
    intro t ht
    obtain ⟨hl, hu, he, hp⟩ := enabled t ht
    exact ⟨hl, hu, he, fun ha => hp (agreed_implies_proposed (b.reachable t) ha)⟩
  obtain ⟨t, ht, value, attempt⟩ := p.repropose start retry
  exact ⟨t, ht, value, by rw [attempt.2.2]; exact List.mem_cons_self⟩

theorem eventually_agreed_stable_consensus {cfg : Config} {leader n : Node}
    {tr : Nat → State Node Request Payload Response} (b : Behavior cfg leader tr)
    (start : Nat) (stable : StableLeader tr n start) (request : Request)
    (receipt : GateReady cfg (tr start) request) (progress : RetryProgress cfg tr n request)
    (consensus : StableConsensusProgress tr n start) :
    EventuallyFrom start (fun t => Agreed (tr t) request) := by
  obtain ⟨w, hw, executed⟩ := eventually_executed b start stable request receipt (progress.localProgress b)
  classical
  apply Classical.byContradiction
  intro never
  have noAgreed : ∀ t, start ≤ t → ¬ Agreed (tr t) request :=
    fun t ht ha => never ⟨t, ht, ha⟩
  have enabled : ∀ t, w ≤ t → RetryEnabled (tr t) n request := by
    intro t ht
    have htStart := Nat.le_trans hw ht
    exact ⟨(stable t htStart).1, (stable t htStart).2,
      propagate (fun u hu => executed_step_mono (b.next u) hu) ht executed,
      noAgreed t htStart⟩
  obtain ⟨t, ht, value, attempt⟩ := progress.repropose w enabled
  obtain ⟨d, hd, item⟩ := consensus t (Nat.le_trans hw ht) (request, value) attempt
  exact noAgreed d (by omega) (List.mem_map_of_mem item)

/-- End-to-end liveness without the stronger global-proposal-buffer contract. -/
theorem eventual_delivery_stable_consensus {cfg : Config} {leader n : Node}
    {tr : Nat → State Node Request Payload Response} (b : Behavior cfg leader tr)
    (stabilizes : Nat) (stable : StableLeader tr n stabilizes) (request : Request)
    (ingress : EventuallyFrom 0 (fun t => GateReady cfg (tr t) request))
    (progress : RetryProgress cfg tr n request)
    (consensus : StableConsensusProgress tr n stabilizes)
    (r : Node) (delivery : DeliveryProgress (fun t => (tr t).core) r) :
    EventuallyFrom 0 (fun t => ∃ value, (request, value) ∈ ((tr t).core.replica r).delivered) := by
  obtain ⟨received, _, ready⟩ := ingress
  let start := max stabilizes received
  have readyNow : GateReady cfg (tr start) request :=
    propagate (fun t ht => gate_step_mono (b.next t) ht) (Nat.le_max_right _ _) ready
  have stableNow : StableLeader tr n start := fun t ht => stable t
    (Nat.le_trans (Nat.le_max_left _ _) ht)
  have consensusNow : StableConsensusProgress tr n start := fun t ht => consensus t
    (Nat.le_trans (Nat.le_max_left _ _) ht)
  obtain ⟨d, _, agreed⟩ := eventually_agreed_stable_consensus b start stableNow request readyNow
    progress consensusNow
  obtain ⟨t, _, value, delivered⟩ := agreed_eventually_delivered b.core r delivery d agreed
  exact ⟨t, Nat.zero_le _, value, delivered⟩

theorem exactly_once_stable_consensus {cfg : Config} {leader n : Node}
    {tr : Nat → State Node Request Payload Response} (b : Behavior cfg leader tr)
    (stabilizes : Nat) (stable : StableLeader tr n stabilizes) (request : Request)
    (ingress : EventuallyFrom 0 (fun t => GateReady cfg (tr t) request))
    (progress : RetryProgress cfg tr n request)
    (consensus : StableConsensusProgress tr n stabilizes)
    (r : Node) (delivery : DeliveryProgress (fun t => (tr t).core) r) :
    EventuallyFrom 0 (fun t => (((tr t).core.replica r).delivered.map Prod.fst).count request = 1) := by
  obtain ⟨t, ht, value, hv⟩ := eventual_delivery_stable_consensus b stabilizes stable request ingress
    progress consensus r delivery
  have member : request ∈ ((tr t).core.replica r).delivered.map Prod.fst := List.mem_map_of_mem hv
  have pos := List.count_pos_iff.mpr member
  have bound := List.nodup_iff_count.mp (at_most_once_delivery (b.reachable t) r) request
  exact ⟨t, ht, by omega⟩

end Resdet.Protocol
