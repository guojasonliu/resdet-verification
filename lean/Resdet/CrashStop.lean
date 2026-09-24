import Resdet.Paper

/-!
Author-confirmed paper scope: crash-stop failures and retries of unfinished
requests. A failed replica never rejoins. The broader protocol library retains
recovery as an optional extension, but it is not part of this paper interface.
-/
namespace Resdet.Paper

variable {Node Request Payload Response : Type}
variable [DecidableEq Node] [DecidableEq Request]

/-- State-level restriction excluding recovery transitions. A crashed node's
historical events may remain in the model; they do not imply that it restarts. -/
def StaysDown (s t : Protocol.State Node Request Payload Response) : Prop :=
  ∀ n, s.up n = false → t.up n = false

structure CrashStopBehavior (cfg : Protocol.Config) (leader : Node)
    (tr : Nat → Protocol.State Node Request Payload Response) : Prop where
  protocol : Protocol.Behavior cfg leader tr
  noRevival : ∀ time, StaysDown (tr time) (tr (time+1))

/-- Delivery liveness is required for replicas which do not fail, not failed ones. -/
def NonFaulty (tr : Nat → Protocol.State Node Request Payload Response) (r : Node) : Prop :=
  ∀ time, (tr time).up r = true

theorem CrashStopBehavior.permanently_down {cfg : Protocol.Config} {leader : Node}
    {tr : Nat → Protocol.State Node Request Payload Response} (b : CrashStopBehavior cfg leader tr)
    (r : Node) {a c : Nat} (order : a ≤ c) (down : (tr a).up r = false) :
    (tr c).up r = false :=
  propagate (fun t ht => b.noRevival t r ht) order down

theorem CrashStopBehavior.nonfaulty_of_eventually_up {cfg : Protocol.Config} {leader : Node}
    {tr : Nat → Protocol.State Node Request Payload Response} (b : CrashStopBehavior cfg leader tr)
    (r : Node) (start : Nat) (up : ∀ t, start ≤ t → (tr t).up r = true) : NonFaulty tr r := by
  intro t
  cases ht : (tr t).up r with
  | true => rfl
  | false =>
      have down := b.permanently_down r (Nat.le_max_left t start) ht
      have alive := up (max t start) (Nat.le_max_right _ _)
      rw [down] at alive
      contradiction

/-- The eventual stable leader cannot have crashed earlier and recovered. -/
theorem CrashStopBehavior.stable_leader_nonfaulty {cfg : Protocol.Config} {leader n : Node}
    {tr : Nat → Protocol.State Node Request Payload Response} (b : CrashStopBehavior cfg leader tr)
    (start : Nat) (stable : Protocol.StableLeader tr n start) : NonFaulty tr n :=
  b.nonfaulty_of_eventually_up n start (fun t ht => (stable t ht).2)

/-- All existing protocol safety results restrict to crash-stop runs. -/
theorem crash_stop_all_safety {cfg : Protocol.Config} {leader : Node}
    {tr : Nat → Protocol.State Node Request Payload Response} (b : CrashStopBehavior cfg leader tr)
    (time : Nat) : Protocol.Safety cfg (tr time) :=
  Protocol.all_safety (b.protocol.reachable time)

theorem theorem_1_crash_stop {cfg : Protocol.Config} {leader : Node}
    {tr : Nat → Protocol.State Node Request Payload Response} (b : CrashStopBehavior cfg leader tr)
    (r t : Node) (a c : Nat) {request : Request} {x y : Response}
    (hx : (request, x) ∈ ((tr a).core.replica r).delivered)
    (hy : (request, y) ∈ ((tr c).core.replica t).delivered) : x = y :=
  theorem_1_safety b.protocol.core r t a c hx hy

/-- The paper's crash-stop liveness theorem. Unfinished requests retry through
the stable leader (ingress/PendingHandlers); no failed handler must recover.
The conclusion is only for non-faulty replicas, and remains exactly once. -/
theorem theorem_2_crash_stop {cfg : Protocol.Config} {leader n : Node}
    {tr : Nat → Protocol.State Node Request Payload Response} (b : CrashStopBehavior cfg leader tr)
    (quorumOne : cfg.quorum = 1) (submitted : Request → Prop)
    (stabilizes : Nat) (stable : Protocol.StableLeader tr n stabilizes)
    (ingress : ∀ request, submitted request → EventuallyFrom 0
      (fun t => ∃ sender payload, (sender, request, payload) ∈ (tr t).ballots))
    (handlers : ∀ request, submitted request → PendingHandlers cfg tr n request)
    (consensus : Protocol.StableConsensusProgress tr n stabilizes)
    (replicas : ∀ r, NonFaulty tr r → DeliveryProgress (fun t => (tr t).core) r) :
    ∀ request, submitted request → ∀ r, NonFaulty tr r →
      ∃ time value, ∀ later, time ≤ later →
        (request, value) ∈ ((tr later).core.replica r).delivered ∧
        (((tr later).core.replica r).delivered.map Prod.fst).count request = 1 :=
  theorem_2_liveness b.protocol quorumOne submitted (NonFaulty tr) stabilizes stable
    ingress handlers consensus replicas

/-- Finite crash-stop traces, used to build checked failover examples. -/
inductive CrashStopReachable (cfg : Protocol.Config) (leader : Node) :
    Protocol.State Node Request Payload Response → Prop
  | init : CrashStopReachable cfg leader (Protocol.initial leader)
  | step {s t} : CrashStopReachable cfg leader s → Protocol.Step cfg s t →
      StaysDown s t → CrashStopReachable cfg leader t

theorem CrashStopReachable.reachable {cfg : Protocol.Config} {leader : Node}
    {s : Protocol.State Node Request Payload Response} (h : CrashStopReachable cfg leader s) :
    Protocol.Reachable cfg leader s := by
  induction h with
  | init => exact .init
  | step _ step _ ih => exact .step ih step

theorem CrashStopReachable.extend {cfg : Protocol.Config} {leader : Node}
    {s : Protocol.State Node Request Payload Response} (h : CrashStopReachable cfg leader s) :
    ∃ tr, CrashStopBehavior cfg leader tr ∧ ∃ finish, ∀ t, finish ≤ t → tr t = s := by
  induction h with
  | init =>
      exact ⟨fun _ => Protocol.initial leader,
        ⟨⟨rfl, fun _ => .stutter _⟩, fun _ _ h => h⟩, 0, fun _ _ => rfl⟩
  | @step s t _ step down ih =>
      obtain ⟨tr, b, finish, steady⟩ := ih
      let tr' := fun k => if k ≤ finish then tr k else t
      have next : ∀ k, Protocol.Step cfg (tr' k) (tr' (k+1)) ∧ StaysDown (tr' k) (tr' (k+1)) := by
        intro k
        by_cases before : k < finish
        · simpa [tr', show k ≤ finish by omega, show k+1 ≤ finish by omega] using
            And.intro (b.protocol.next k) (b.noRevival k)
        · by_cases atEnd : k = finish
          · subst k
            simpa [tr', steady finish (Nat.le_refl _), show ¬ finish+1 ≤ finish by omega] using
              And.intro step down
          · simpa [tr', show ¬ k ≤ finish by omega, show ¬ k+1 ≤ finish by omega] using
              And.intro (Protocol.Step.stutter (cfg := cfg) t) (show StaysDown t t from fun _ h => h)
      refine ⟨tr', ⟨⟨?_, fun k => (next k).1⟩, fun k => (next k).2⟩, finish+1, ?_⟩
      · simpa [tr'] using b.protocol.init
      · intro k hk
        simp [tr', show ¬ k ≤ finish by omega]

end Resdet.Paper
