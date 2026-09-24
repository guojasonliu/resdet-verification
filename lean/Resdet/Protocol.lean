import Resdet.CachedDelivery

/-!
Fuller unbounded protocol model. Consensus safety is still abstracted by one
append-only log. Histories and delivery state survive crashes. Selection is
global as in the existing TLA+ model. No unsafe direct-delivery fallback exists.
-/
namespace Resdet.Protocol

structure Config where
  quorum : Nat
  quorumPositive : 0 < quorum
  crashes : Bool := false
  timeoutFallback : Bool := false

abbrev Ballot (Node Request Payload : Type) := Node × Request × Payload
abbrev Choice (Request Payload : Type) := Request × Payload × Bool
abbrev Dispatch (Node Request : Type) := Node × Request × Option Node
abbrev Execution (Node Request Response : Type) := Node × Request × Response

structure State (Node Request Payload Response : Type) where
  core : Resdet.State Node Request Response
  seen : Node → List Request
  leader : Option Node
  up : Node → Bool
  ballots : List (Ballot Node Request Payload)
  choices : List (Choice Request Payload)
  dispatches : List (Dispatch Node Request)
  executions : List (Execution Node Request Response)
  observed : List (Item Request Response)
  proposed : List (Item Request Response)

variable {Node Request Payload Response : Type}
variable [DecidableEq Node] [DecidableEq Request]

def initial (leader : Node) : State Node Request Payload Response :=
  ⟨Resdet.initial, fun _ => [], some leader, fun _ => true, [], [], [], [], [], []⟩

def Selected (s : State Node Request Payload Response) (request : Request) : Prop :=
  ∃ payload fallback, (request, payload, fallback) ∈ s.choices

/-- A finite certificate counts distinct matching callers, never duplicate votes. -/
def Justified (q : Nat) (ballots : List (Ballot Node Request Payload))
    (choice : Choice Request Payload) : Prop :=
  if choice.2.2 then ∃ voter, (voter, choice.1, choice.2.1) ∈ ballots
  else ∃ voters : List Node, voters.Nodup ∧ q ≤ voters.length ∧
    ∀ voter ∈ voters, (voter, choice.1, choice.2.1) ∈ ballots

def CacheCoherent (s : State Node Request Payload Response) : Prop :=
  ∀ r, s.seen r = (s.core.replica r).delivered.map Prod.fst

def process (s : State Node Request Payload Response) (r : Node)
    (batch : List (Item Request Response)) :=
  let result := applyCached batch (s.seen r) (s.core.replica r).delivered
  let replicas := fun n =>
    if n = r then
      { s.core.replica n with processed := (s.core.replica n).processed + 1,
                              delivered := result.2 }
    else s.core.replica n
  { s with core := { s.core with replica := replicas },
           seen := fun n => if n = r then result.1 else s.seen n }

inductive Step (cfg : Config) : State Node Request Payload Response →
    State Node Request Payload Response → Prop
  | vote (s) (n request payload) (live : s.up n = true)
      (fresh : ∀ p, (n, request, p) ∉ s.ballots) :
      Step cfg s { s with ballots := (n, request, payload) :: s.ballots }
  | select (s) (n request payload fallback)
      (leader : s.leader = some n) (live : s.up n = true)
      (fresh : ¬ Selected s request)
      (evidence : Justified cfg.quorum s.ballots (request, payload, fallback))
      (allowed : fallback = true → cfg.timeoutFallback = true) :
      Step cfg s { s with choices := (request, payload, fallback) :: s.choices }
  | dispatch (s) (n request) (leader : s.leader = some n) (live : s.up n = true)
      (selected : Selected s request)
      (fresh : ∀ l, (n, request, l) ∉ s.dispatches)
      (once : cfg.crashes = false → ∀ d ∈ s.dispatches, d.2.1 ≠ request) :
      Step cfg s { s with dispatches := (n, request, s.leader) :: s.dispatches }
  | respond (s) (n request value)
      (dispatched : ∃ l, (n, request, l) ∈ s.dispatches)
      (fresh : ∀ v, (n, request, v) ∉ s.executions) :
      Step cfg s { s with
        executions := (n, request, value) :: s.executions
        observed := (request, value) :: s.observed }
  | propose (s) (n request value) (leader : s.leader = some n) (live : s.up n = true)
      (executed : (n, request, value) ∈ s.executions)
      (fresh : (request, value) ∉ s.proposed) :
      Step cfg s { s with proposed := (request, value) :: s.proposed }
  /-- A real proposal attempt by the current leader, even if an older leader
  buffered the same item. Required when CG3 covers only stable-leader attempts. -/
  | repropose (s) (n request value) (leader : s.leader = some n) (live : s.up n = true)
      (executed : (n, request, value) ∈ s.executions)
      (buffered : (request, value) ∈ s.proposed) :
      Step cfg s { s with proposed := (request, value) :: s.proposed }
  | decide (s) (batch : List (Item Request Response))
      (valid : ∀ item ∈ batch, item ∈ s.proposed) :
      Step cfg s { s with core := appendBatch s.core batch }
  | learn (s) (r slot) (live : s.up r = true) (valid : slot < s.core.log.length) :
      Step cfg s { s with core := learnSlot s.core r slot }
  | process (s) (r batch) (live : s.up r = true)
      (learned : (s.core.replica r).processed ∈ (s.core.replica r).learned)
      (entry : s.core.log[(s.core.replica r).processed]? = some batch) :
      Step cfg s (process s r batch)
  | crash (s) (n) (enabled : cfg.crashes = true) (live : s.up n = true) :
      Step cfg s { s with
        up := fun r => if r = n then false else s.up r
        leader := if s.leader = some n then none else s.leader }
  | recover (s) (n) (enabled : cfg.crashes = true) (down : s.up n = false) :
      Step cfg s { s with up := fun r => if r = n then true else s.up r }
  | elect (s) (n) (enabled : cfg.crashes = true)
      (vacant : s.leader = none) (live : s.up n = true) :
      Step cfg s { s with leader := some n }
  | stutter (s) : Step cfg s s

inductive Reachable (cfg : Config) (leader : Node) : State Node Request Payload Response → Prop
  | init : Reachable cfg leader (initial leader)
  | step {s t} : Reachable cfg leader s → Step cfg s t → Reachable cfg leader t

theorem process_core (s : State Node Request Payload Response) (h : CacheCoherent s)
    (r : Node) (batch : List (Item Request Response)) :
    (process s r batch).core = processBatch s.core r batch := by
  simp only [process, applyCached_correct batch _ _ (h r), processBatch]
  congr 1
  funext n
  by_cases hn : n = r
  · subst n; simp
  · simp [hn]

theorem step_cache {cfg : Config} {s t : State Node Request Payload Response}
    (h : CacheCoherent s) (step : Step cfg s t) : CacheCoherent t := by
  cases step with
  | learn r slot _ _ =>
      intro n
      by_cases hn : n = r <;> simpa [learnSlot, hn] using h n
  | process r batch _ _ _ =>
      intro n
      simp only [process, applyCached_correct batch _ _ (h r)]
      by_cases hn : n = r
      · subst n; simp
      · simpa [hn] using h n
  | _ => exact h

/-- A proved forward simulation, not an assumed invariant in the full model. -/
theorem step_refines {cfg : Config} {s t : State Node Request Payload Response}
    (h : CacheCoherent s) (step : Step cfg s t) : Resdet.Step s.core t.core := by
  cases step with
  | decide batch _ => exact .append _ batch
  | learn r slot _ valid => exact .learn _ r slot valid
  | process r batch _ learned entry =>
      rw [process_core s h]
      exact .process _ r batch learned entry
  | _ => exact .stutter _

theorem reachable_cache {cfg : Config} {leader : Node} {s : State Node Request Payload Response}
    (h : Reachable cfg leader s) : CacheCoherent s := by
  induction h with
  | init => intro r; rfl
  | step _ step ih => exact step_cache ih step

theorem reachable_refines {cfg : Config} {leader : Node}
    {s : State Node Request Payload Response} (h : Reachable cfg leader s) :
    Resdet.Reachable s.core := by
  induction h with
  | init => exact .init
  | step reach step ih => exact .step ih (step_refines (reachable_cache reach) step)

end Resdet.Protocol
