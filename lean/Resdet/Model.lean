import Resdet.Delivery

/-!
An unbounded transition-system abstraction of Resdet's delivery core.

Consensus is an append-only global log, not an implementation of Raft.
Learning is arbitrarily reordered; only the next learned slot can be processed.
Slots are zero-based. No fairness, finite-state bound, or response uniqueness
is assumed. The independent `delivered` field is updated incrementally.
-/
namespace Resdet

structure ReplicaState (Request Response : Type) where
  processed : Nat := 0
  learned : List Nat := []
  delivered : List (Item Request Response) := []
  deriving DecidableEq

structure State (Node Request Response : Type) where
  log : List (List (Item Request Response))
  replica : Node → ReplicaState Request Response

variable {Node Request Response : Type} [DecidableEq Node] [DecidableEq Request]

def initial : State Node Request Response := ⟨[], fun _ => {}⟩

def appendBatch (s : State Node Request Response) (batch : List (Item Request Response)) :=
  { s with log := s.log ++ [batch] }

def learnSlot (s : State Node Request Response) (r : Node) (slot : Nat) :=
  { s with replica := fun n =>
      if n = r then { s.replica n with learned := slot :: (s.replica n).learned }
      else s.replica n }

def processBatch (s : State Node Request Response) (r : Node)
    (batch : List (Item Request Response)) :=
  { s with replica := fun n =>
      if n = r then
        { s.replica n with
          processed := (s.replica n).processed + 1
          delivered := applyItems batch (s.replica n).delivered }
      else s.replica n }

/-- Only these rules generate executions. `process` checks the actual log
entry and the learned next slot; it does not assume any safety invariant. -/
inductive Step : State Node Request Response → State Node Request Response → Prop
  | append (s) (batch) : Step s (appendBatch s batch)
  | learn (s) (r) (slot) (decided : slot < s.log.length) : Step s (learnSlot s r slot)
  | process (s) (r) (batch)
      (learned : (s.replica r).processed ∈ (s.replica r).learned)
      (entry : s.log[(s.replica r).processed]? = some batch) :
      Step s (processBatch s r batch)
  | stutter (s) : Step s s

inductive Reachable : State Node Request Response → Prop
  | init : Reachable initial
  | step {s t} : Reachable s → Step s t → Reachable t

/-- The inductive strengthening, not a precondition of the transition rules. -/
structure Invariant (s : State Node Request Response) : Prop where
  processedWithinLog : ∀ r, (s.replica r).processed ≤ s.log.length
  learnedOnlyDecided : ∀ r slot, slot ∈ (s.replica r).learned → slot < s.log.length
  processedPrefixLearned : ∀ r slot, slot < (s.replica r).processed →
    slot ∈ (s.replica r).learned
  appliedPrefixCorrect : ∀ r, (s.replica r).delivered =
    dedup ((s.log.take (s.replica r).processed).flatten)

omit [DecidableEq Node] in
theorem initial_invariant : Invariant (initial : State Node Request Response) := by
  constructor <;> simp [initial, dedup, dedupFrom]

theorem step_preserves_invariant {s t : State Node Request Response}
    (inv : Invariant s) (step : Step s t) : Invariant t := by
  cases step with
  | stutter => exact inv
  | append batch =>
      constructor
      · intro r
        have := inv.processedWithinLog r
        simp only [appendBatch, List.length_append, List.length_singleton]
        omega
      · intro r slot hs
        have := inv.learnedOnlyDecided r slot hs
        simp only [appendBatch, List.length_append, List.length_singleton]
        omega
      · exact inv.processedPrefixLearned
      · intro r
        simp only [appendBatch]
        rw [List.take_append_of_le_length (inv.processedWithinLog r)]
        exact inv.appliedPrefixCorrect r
  | learn r slot decided =>
      constructor
      · intro n
        by_cases hn : n = r
        · subst n; simpa [learnSlot] using inv.processedWithinLog r
        · simpa [learnSlot, hn] using inv.processedWithinLog n
      · intro n index hi
        by_cases hn : n = r
        · subst n
          simp [learnSlot] at hi
          rcases hi with rfl | hi
          · exact decided
          · exact inv.learnedOnlyDecided r index hi
        · exact inv.learnedOnlyDecided n index (by simpa [learnSlot, hn] using hi)
      · intro n index hi
        by_cases hn : n = r
        · subst n
          simp [learnSlot] at hi ⊢
          exact Or.inr (inv.processedPrefixLearned r index hi)
        · simpa [learnSlot, hn] using
            inv.processedPrefixLearned n index (by simpa [learnSlot, hn] using hi)
      · intro n
        by_cases hn : n = r
        · subst n; simpa [learnSlot] using inv.appliedPrefixCorrect r
        · simpa [learnSlot, hn] using inv.appliedPrefixCorrect n
  | process r batch learned entry =>
      have bound : (s.replica r).processed < s.log.length :=
        (List.getElem?_eq_some_iff.mp entry).1
      constructor
      · intro n
        by_cases hn : n = r
        · subst n; simpa [processBatch] using Nat.succ_le_of_lt bound
        · simpa [processBatch, hn] using inv.processedWithinLog n
      · intro n index hi
        by_cases hn : n = r
        · subst n
          exact inv.learnedOnlyDecided r index (by simpa [processBatch] using hi)
        · exact inv.learnedOnlyDecided n index (by simpa [processBatch, hn] using hi)
      · intro n index hi
        by_cases hn : n = r
        · subst n
          simp [processBatch] at hi ⊢
          by_cases heq : index = (s.replica r).processed
          · simpa [heq] using learned
          · exact inv.processedPrefixLearned r index (by omega)
        · simpa [processBatch, hn] using
            inv.processedPrefixLearned n index (by simpa [processBatch, hn] using hi)
      · intro n
        by_cases hn : n = r
        · subst n
          simp only [processBatch, ite_true]
          rw [List.take_succ, entry]
          simp only [Option.toList_some, List.flatten_append, List.flatten_cons,
            List.flatten_nil, List.append_nil]
          rw [inv.appliedPrefixCorrect r]
          simp only [dedup_eq_applyItems, applyItems_append]
        · simpa [processBatch, hn] using inv.appliedPrefixCorrect n

theorem reachable_invariant {s : State Node Request Response} (h : Reachable s) :
    Invariant s := by
  induction h with
  | init => exact initial_invariant
  | step _ step ih => exact step_preserves_invariant ih step

end Resdet
