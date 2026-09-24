import Resdet
import ProtocolTests

namespace Resdet.Paper.Tests

def ordered : List (Item Nat Nat) := [(10, 1), (20, 2), (10, 99), (30, 3), (20, 77)]
def batched : List (List (Item Nat Nat)) :=
  [[(10, 1), (20, 2)], [], [(10, 99)], [(30, 3), (20, 77)]]

theorem batch_boundaries_do_not_change_result :
    applyBatches batched [] = applyBatches (ordered.map (fun item => [item])) [] :=
  rebatching_preserves_delivery (by decide) []

theorem first_not_last_response :
    applyBatches batched [] = [(10, 1), (20, 2), (30, 3)] ∧
    firstFor 10 ordered = some (10, 1) := by decide

theorem recovered_delivery_is_first_committed :
    firstFor 1 Protocol.Tests.p16.core.log.flatten = some (1, 9) :=
  first_committed_response (Protocol.reachable_refines Protocol.Tests.recovery_run)
    false (by decide)

theorem one_core_arrival_needs_no_majority :
    Protocol.GateReady Protocol.Tests.cfg Protocol.Tests.p1 1 :=
  single_arrival_ready (by decide) (sender := false) (payload := 42) (by decide)

/-- Supplementary wider-model example with recovery. The current paper's
no-recovery witness is CrashStopTests.crash_stop_contracts_satisfiable. -/
theorem paper_contracts_satisfiable :
    ∃ (tr : Nat → Protocol.Tests.S) (finish : Nat),
      Protocol.Behavior Protocol.Tests.cfg false tr ∧
      Protocol.StableLeader tr true finish ∧
      (∃ sender payload, (sender, 1, payload) ∈ (tr finish).ballots) ∧
      PendingHandlers Protocol.Tests.cfg tr true 1 ∧
      Protocol.StableConsensusProgress tr true finish ∧
      ∀ r, DeliveryProgress (fun t => (tr t).core) r := by
  obtain ⟨tr, finish, b, stable, ready, handlers, consensus, delivery⟩ :=
    Protocol.Tests.retry_contracts_satisfiable
  have arrival : ∃ sender payload, (sender, 1, payload) ∈ (tr finish).ballots := by
    obtain ⟨payload, fallback, evidence, allowed⟩ := ready
    cases fallback with
    | false =>
        obtain ⟨voters, _, enough, matching⟩ := evidence
        cases voters with
        | nil => simp [Protocol.Tests.cfg] at enough
        | cons sender rest => exact ⟨sender, payload, matching sender (by simp)⟩
    | true => exact False.elim (Bool.noConfusion (allowed rfl))
  exact ⟨tr, finish, b, stable, arrival, .ofRetry handlers, consensus, delivery⟩

/-- Supplementary regression outside the confirmed crash-stop paper scope.
A deliberately incomplete recovery interpretation of Fig. 7, NOT a second
Resdet model or a counterexample satisfying all main-model progress premises.
It isolates why keeping the request dedup marker but dropping the associated
unfinished handler is insufficient. Repeated handle_request calls then all
return at the duplicate check, despite request-arrival progress. -/
structure Admission where
  seen : List Nat := []
  running : List Nat := []
  proposals : List Nat := []
  deriving DecidableEq

def receive (s : Admission) (request : Nat) : Admission :=
  if request ∈ s.seen then s
  else { s with seen := request :: s.seen, running := request :: s.running }

def crashDroppingHandler (s : Admission) : Admission := { s with running := [] }
def stranded : Admission := crashDroppingHandler (receive {} 1)

def retryRequests : Nat → Admission
  | 0 => stranded
  | count + 1 => receive (retryRequests count) 1

theorem recovery_marker_counterexample (count : Nat) :
    retryRequests count = stranded := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [retryRequests, ih] using (show receive stranded 1 = stranded by decide)

theorem retries_without_resumption_stay_pending (count : Nat) :
    1 ∈ (retryRequests count).seen ∧ (retryRequests count).running = [] ∧
      (retryRequests count).proposals = [] := by
  rw [recovery_marker_counterexample]
  decide

end Resdet.Paper.Tests
