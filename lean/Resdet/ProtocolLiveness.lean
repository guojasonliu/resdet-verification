import Resdet.Temporal

namespace Resdet.Protocol

variable {Node Request Payload Response : Type}
variable [DecidableEq Node] [DecidableEq Request]

def Dispatched (s : State Node Request Payload Response) (n : Node) (request : Request) :=
  ∃ l, (n, request, l) ∈ s.dispatches
def Executed (s : State Node Request Payload Response) (n : Node) (request : Request) :=
  ∃ value, (n, request, value) ∈ s.executions
def Proposed (s : State Node Request Payload Response) (request : Request) :=
  ∃ value, (request, value) ∈ s.proposed
def GateReady (cfg : Config) (s : State Node Request Payload Response) (request : Request) :=
  ∃ payload fallback, Justified cfg.quorum s.ballots (request, payload, fallback) ∧
    (fallback = true → cfg.timeoutFallback = true)

structure Behavior (cfg : Config) (leader : Node)
    (tr : Nat → State Node Request Payload Response) : Prop where
  init : tr 0 = initial leader
  next : ∀ t, Step cfg (tr t) (tr (t + 1))

theorem Behavior.reachable {cfg : Config} {leader : Node}
    {tr : Nat → State Node Request Payload Response} (b : Behavior cfg leader tr) (t : Nat) :
    Reachable cfg leader (tr t) := by
  induction t with
  | zero => rw [b.init]; exact .init
  | succ t ih => exact .step ih (b.next t)

theorem Behavior.core {cfg : Config} {leader : Node}
    {tr : Nat → State Node Request Payload Response} (b : Behavior cfg leader tr) :
    Resdet.Behavior (fun t => (tr t).core) := by
  constructor
  · simp [b.init, initial]
  · intro t
    exact step_refines (reachable_cache (b.reachable t)) (b.next t)

theorem gate_step_mono {cfg : Config} {s t : State Node Request Payload Response}
    (step : Step cfg s t) {request : Request} (h : GateReady cfg s request) :
    GateReady cfg t request := by
  obtain ⟨p, f, evidence, allowed⟩ := h
  cases step with
  | vote => exact ⟨p, f, justified_mono
      (List.subset_cons_of_subset _ (fun _ h => h)) evidence, allowed⟩
  | _ => exact ⟨p, f, evidence, allowed⟩

theorem dispatched_step_mono {cfg : Config} {s t : State Node Request Payload Response}
    (step : Step cfg s t) {n : Node} {request : Request} (h : Dispatched s n request) :
    Dispatched t n request := by
  obtain ⟨l, hl⟩ := h
  cases step with
  | dispatch => exact ⟨l, List.mem_cons_of_mem _ hl⟩
  | _ => exact ⟨l, hl⟩

theorem executed_step_mono {cfg : Config} {s t : State Node Request Payload Response}
    (step : Step cfg s t) {n : Node} {request : Request} (h : Executed s n request) :
    Executed t n request := by
  obtain ⟨v, hv⟩ := h
  cases step with
  | respond => exact ⟨v, List.mem_cons_of_mem _ hv⟩
  | _ => exact ⟨v, hv⟩

theorem proposals_step_mono {cfg : Config} {s t : State Node Request Payload Response}
    (step : Step cfg s t) : s.proposed ⊆ t.proposed := by
  cases step with
  | propose => exact List.subset_cons_of_subset _ (fun _ h => h)
  | repropose => exact List.subset_cons_of_subset _ (fun _ h => h)
  | _ => exact fun _ h => h

theorem dispatch_available {cfg : Config} {leader n : Node}
    {s : State Node Request Payload Response} (reach : Reachable cfg leader s)
    (hl : s.leader = some n) {request : Request} (fresh : ¬ Dispatched s n request) :
    cfg.crashes = false → ∀ d ∈ s.dispatches, d.2.1 ≠ request := by
  intro hc d hd same
  have hn : n = leader := Option.some.inj (hl.symm.trans (leader_without_crashes reach hc))
  have sender := senders_without_crashes reach hc d hd
  rcases d with ⟨node, rid, snapshot⟩
  simp only at same sender
  subst rid
  have en : node = n := sender.trans hn.symm
  exact fresh ⟨snapshot, by simpa only [en] using hd⟩

def SelectEnabled (cfg : Config) (s : State Node Request Payload Response)
    (n : Node) (request : Request) :=
  s.leader = some n ∧ s.up n = true ∧ GateReady cfg s request ∧ ¬ Selected s request
def DispatchEnabled (cfg : Config) (s : State Node Request Payload Response)
    (n : Node) (request : Request) :=
  s.leader = some n ∧ s.up n = true ∧ Selected s request ∧ ¬ Dispatched s n request ∧
    (cfg.crashes = false → ∀ d ∈ s.dispatches, d.2.1 ≠ request)
def RespondEnabled (s : State Node Request Payload Response) (n : Node) (request : Request) :=
  Dispatched s n request ∧ ¬ Executed s n request
def ProposeEnabled (s : State Node Request Payload Response) (n : Node) (request : Request) :=
  s.leader = some n ∧ s.up n = true ∧ Executed s n request ∧ ¬ Proposed s request

/-- Per-request action fairness, not fairness of an aggregate action over
infinitely many requests. Respond fairness represents the downstream contract.
Occurrences record the immediate effect of the relevant handler stage. -/
structure LocalProgress (cfg : Config) (tr : Nat → State Node Request Payload Response)
    (n : Node) (request : Request) : Prop where
  select : WeakFair (fun t => SelectEnabled cfg (tr t) n request)
    (fun t => Selected (tr (t+1)) request)
  dispatch : WeakFair (fun t => DispatchEnabled cfg (tr t) n request)
    (fun t => Dispatched (tr (t+1)) n request)
  respond : WeakFair (fun t => RespondEnabled (tr t) n request)
    (fun t => Executed (tr (t+1)) n request)
  propose : WeakFair (fun t => ProposeEnabled (tr t) n request)
    (fun t => Proposed (tr (t+1)) request)

/-- CG3(1) in the stabilized suffix. Faults and elections may precede `start`. -/
def StableLeader (tr : Nat → State Node Request Payload Response) (n : Node) (start : Nat) :=
  ∀ t, start ≤ t → (tr t).leader = some n ∧ (tr t).up n = true

theorem eventually_executed {cfg : Config} {leader n : Node}
    {tr : Nat → State Node Request Payload Response} (b : Behavior cfg leader tr)
    (start : Nat) (stable : StableLeader tr n start) (request : Request)
    (receipt : GateReady cfg (tr start) request) (progress : LocalProgress cfg tr n request) :
    EventuallyFrom start (fun t => Executed (tr t) n request) := by
  have select : EventuallyFrom start (fun t => Selected (tr t) request) := by
    apply fair_progress (p := fun t => GateReady cfg (tr t) request)
      (enabled := fun t => SelectEnabled cfg (tr t) n request)
      (occurs := fun t => Selected (tr (t+1)) request)
    · intro a c hac hp
      exact propagate (fun t ht => gate_step_mono (b.next t) ht) hac hp
    · intro t ht hp hq
      exact ⟨(stable t ht).1, (stable t ht).2, hp, hq⟩
    · exact fun _ _ h => h
    · exact progress.select
    · exact receipt
  obtain ⟨u, hu, selected⟩ := select
  have dispatch : EventuallyFrom u (fun t => Dispatched (tr t) n request) := by
    apply fair_progress (p := fun t => Selected (tr t) request)
      (enabled := fun t => DispatchEnabled cfg (tr t) n request)
      (occurs := fun t => Dispatched (tr (t+1)) n request)
    · intro a c hac hp
      exact propagate (fun t ht => step_selected_mono (b.next t) ht) hac hp
    · intro t ht hp hq
      have leaderNow := stable t (Nat.le_trans hu ht)
      exact ⟨leaderNow.1, leaderNow.2, hp, hq, dispatch_available (b.reachable t) leaderNow.1 hq⟩
    · exact fun _ _ h => h
    · exact progress.dispatch
    · exact selected
  obtain ⟨v, hv, dispatched⟩ := dispatch
  have respond : EventuallyFrom v (fun t => Executed (tr t) n request) := by
    apply fair_progress (p := fun t => Dispatched (tr t) n request)
      (enabled := fun t => RespondEnabled (tr t) n request)
      (occurs := fun t => Executed (tr (t+1)) n request)
    · intro a c hac hp
      exact propagate (fun t ht => dispatched_step_mono (b.next t) ht) hac hp
    · exact fun _ _ hp hq => ⟨hp, hq⟩
    · exact fun _ _ h => h
    · exact progress.respond
    · exact dispatched
  obtain ⟨w, hw, executed⟩ := respond
  exact ⟨w, by omega, executed⟩

theorem eventually_proposed {cfg : Config} {leader n : Node}
    {tr : Nat → State Node Request Payload Response} (b : Behavior cfg leader tr)
    (start : Nat) (stable : StableLeader tr n start) (request : Request)
    (receipt : GateReady cfg (tr start) request) (progress : LocalProgress cfg tr n request) :
    EventuallyFrom start (fun t => Proposed (tr t) request) := by
  obtain ⟨w, hw, executed⟩ := eventually_executed b start stable request receipt progress
  have propose : EventuallyFrom w (fun t => Proposed (tr t) request) := by
    apply fair_progress (p := fun t => Executed (tr t) n request)
      (enabled := fun t => ProposeEnabled (tr t) n request)
      (occurs := fun t => Proposed (tr (t+1)) request)
    · intro a c hac hp
      exact propagate (fun t ht => executed_step_mono (b.next t) ht) hac hp
    · intro t ht hp hq
      have leaderNow := stable t (by omega)
      exact ⟨leaderNow.1, leaderNow.2, hp, hq⟩
    · exact fun _ _ h => h
    · exact progress.propose
    · exact executed
  obtain ⟨z, hz, proposed⟩ := propose
  exact ⟨z, by omega, proposed⟩

/-- Consensus progress for the persistent global proposal buffer of this model.
This requires pending proposals to be retried across elections; it is stronger
than a guarantee only about fresh proposals by the final leader. -/
def ConsensusProgress (tr : Nat → State Node Request Payload Response) :=
  ∀ start item, item ∈ (tr start).proposed →
    EventuallyFrom start (fun t => item ∈ (tr t).core.log.flatten)

/-- Conditional end-to-end liveness: ingress, handlers, consensus, learning,
and finite-prefix processing are connected without assuming eventual delivery. -/
theorem eventual_delivery {cfg : Config} {leader n : Node}
    {tr : Nat → State Node Request Payload Response} (b : Behavior cfg leader tr)
    (stabilizes : Nat) (stable : StableLeader tr n stabilizes) (request : Request)
    (ingress : EventuallyFrom 0 (fun t => GateReady cfg (tr t) request))
    (localProgress : LocalProgress cfg tr n request) (consensus : ConsensusProgress tr)
    (r : Node) (delivery : DeliveryProgress (fun t => (tr t).core) r) :
    EventuallyFrom 0 (fun t => ∃ value, (request, value) ∈ ((tr t).core.replica r).delivered) := by
  obtain ⟨received, _, ready⟩ := ingress
  let start := max stabilizes received
  have readyNow : GateReady cfg (tr start) request :=
    propagate (fun t ht => gate_step_mono (b.next t) ht) (Nat.le_max_right _ _) ready
  have stableNow : StableLeader tr n start := fun t ht => stable t
    (Nat.le_trans (Nat.le_max_left _ _) ht)
  obtain ⟨p, _, value, proposed⟩ := eventually_proposed b start stableNow request readyNow localProgress
  obtain ⟨d, _, decided⟩ := consensus p (request, value) proposed
  have idInLog : request ∈ (tr d).core.log.flatten.map Prod.fst := List.mem_map_of_mem decided
  obtain ⟨t, _, delivered⟩ := agreed_eventually_delivered b.core r delivery d idInLog
  exact ⟨t, Nat.zero_le _, delivered⟩

/-- Exactly-once *workflow delivery* under the same progress contracts;
this does not mean exactly-once external execution. -/
theorem eventual_exactly_once {cfg : Config} {leader n : Node}
    {tr : Nat → State Node Request Payload Response} (b : Behavior cfg leader tr)
    (stabilizes : Nat) (stable : StableLeader tr n stabilizes) (request : Request)
    (ingress : EventuallyFrom 0 (fun t => GateReady cfg (tr t) request))
    (localProgress : LocalProgress cfg tr n request) (consensus : ConsensusProgress tr)
    (r : Node) (delivery : DeliveryProgress (fun t => (tr t).core) r) :
    EventuallyFrom 0 (fun t => (((tr t).core.replica r).delivered.map Prod.fst).count request = 1) := by
  obtain ⟨t, ht, value, hv⟩ := eventual_delivery b stabilizes stable request ingress
    localProgress consensus r delivery
  have member : request ∈ ((tr t).core.replica r).delivered.map Prod.fst := List.mem_map_of_mem hv
  have pos := List.count_pos_iff.mpr member
  have bound := List.nodup_iff_count.mp (at_most_once_delivery (b.reachable t) r) request
  exact ⟨t, ht, by omega⟩

end Resdet.Protocol
