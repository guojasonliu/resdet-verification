import Resdet
import ProtocolTests
import PaperTests
import CrashStopTests

/-! Small kernel-checked examples, including a reachable nontrivial execution.
These are regression checks, not substitutes for the parameterized theorems. -/
namespace Resdet.Tests

abbrev ExampleState := State Bool Nat Nat

def batch0 : List (Item Nat Nat) := [(1, 7), (1, 9), (2, 8)]
def batch1 : List (Item Nat Nat) := [(2, 99), (3, 10)]
def s0 : ExampleState := initial
def s1 := appendBatch s0 batch0
def s2 := appendBatch s1 batch1
-- false learns slot 1 before slot 0, and must wait before processing.
def s3 := learnSlot s2 false 1
def s4 := learnSlot s3 false 0
def s5 := processBatch s4 false batch0
def s6 := processBatch s5 false batch1
-- true catches up only as far as the first batch.
def s7 := learnSlot s6 true 0
def s8 := processBatch s7 true batch0

theorem sample_reachable : Reachable s8 := by
  have h1 : Reachable s1 := .step .init (.append s0 batch0)
  have h2 : Reachable s2 := .step h1 (.append s1 batch1)
  have h3 : Reachable s3 := .step h2 (.learn s2 false 1 (by decide))
  have h4 : Reachable s4 := .step h3 (.learn s3 false 0 (by decide))
  have h5 : Reachable s5 := .step h4 (.process s4 false batch0 (by decide) (by decide))
  have h6 : Reachable s6 := .step h5 (.process s5 false batch1 (by decide) (by decide))
  have h7 : Reachable s7 := .step h6 (.learn s6 true 0 (by decide))
  exact .step h7 (.process s7 true batch0 (by decide) (by decide))

theorem next_slot_not_yet_learned : (s3.replica false).processed ∉
    (s3.replica false).learned := by decide

theorem learned_out_of_order_but_not_delivered : (s3.replica false).delivered = [] := by decide

theorem full_delivery : (s8.replica false).delivered = [(1, 7), (2, 8), (3, 10)] := by decide

theorem lagging_delivery : (s8.replica true).delivered = [(1, 7), (2, 8)] := by decide

theorem example_agreement : 7 = (7 : Nat) :=
  response_agreement sample_reachable false true (request := 1) (by decide) (by decide)

-- Boundary cases: empty batches, duplicate slots, and conflicting responses.
theorem empty_batch : applyItems [] [(1, 7)] = [(1, 7)] := by decide

theorem duplicate_slot : applyItems batch0 (applyItems batch0 []) = [(1, 7), (2, 8)] := by decide

theorem conflicting_response : dedup [(1, 7), (1, 999)] = [(1, 7)] := by decide

-- Counterexamples to weakened handlers, deliberately NOT constructors of Step.
def noDedupOutput : List (Item Nat Nat) := [] ++ [(1, 7), (1, 9)]

theorem no_dedup_breaks_at_most_once :
    ¬ (noDedupOutput.map Prod.fst).Nodup := by decide

def conflictLog : List (List (Item Nat Nat)) := [[(1, 7)], [(1, 9)]]

def skippedPrefix : ExampleState :=
  { log := conflictLog
    replica := fun r =>
      if r then ⟨2, [0, 1], [(1, 9)]⟩ else ⟨1, [0, 1], [(1, 7)]⟩ }

theorem skipping_prefix_breaks_agreement :
    (1, 7) ∈ (skippedPrefix.replica false).delivered ∧
    (1, 9) ∈ (skippedPrefix.replica true).delivered ∧ (7 : Nat) ≠ 9 := by decide

theorem skipped_prefix_unreachable : ¬ Reachable skippedPrefix := by
  intro h
  have bad : (7 : Nat) = 9 := response_agreement h false true (request := 1)
    (by decide) (by decide)
  exact (by decide : (7 : Nat) ≠ 9) bad

def earlyDelivery : ExampleState :=
  { log := [], replica := fun _ => ⟨0, [], [(1, 7)]⟩ }

theorem early_delivery_unreachable : ¬ Reachable earlyDelivery := by
  intro h
  have bad := delivered_in_log h false (item := (1, 7)) (by decide)
  simp [earlyDelivery] at bad

end Resdet.Tests
