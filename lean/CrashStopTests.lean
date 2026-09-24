import Resdet

namespace Resdet.Paper.CrashStopTests
open Protocol

abbrev Node := Fin 3
abbrev S := Protocol.State Node Nat Nat Nat
local instance (s t : S) : Decidable (StaysDown s t) :=
  inferInstanceAs (Decidable (∀ n, s.up n = false → t.up n = false))

def cfg : Config := ⟨1, by decide, true, false⟩
def s0 : S := Protocol.initial 0
def s1 := { s0 with ballots := [(0, 1, 42)] }
def s2 := { s1 with choices := [(1, 42, false)] }
def s3 := { s2 with dispatches := [(0, 1, some 0)] }
def s4 := { s3 with executions := [(0, 1, 7)], observed := [(1, 7)] }
def s5 := { s4 with proposed := [(1, 7)] }
def s6 := { s5 with up := fun r => if r = 0 then false else s5.up r, leader := none }
def s7 := { s6 with leader := some 1 }
def s8 := { s7 with dispatches := (1, 1, some 1) :: s7.dispatches }
def s9 := { s8 with
  executions := (1, 1, 9) :: s8.executions
  observed := (1, 9) :: s8.observed }
def s10 := { s9 with proposed := (1, 9) :: s9.proposed }
-- The failed leader's old proposal need never commit.
def batch : List (Item Nat Nat) := [(1, 9)]
def s11 := { s10 with core := appendBatch s10.core batch }
def s12 := { s11 with core := learnSlot s11.core 1 0 }
def s13 := Protocol.process s12 1 batch
def s14 := { s13 with core := learnSlot s13.core 2 0 }
def s15 := Protocol.process s14 2 batch

/-- Three replicas, one permanently crashed leader, and a retry by its successor.
Only the two survivors learn/deliver; no recovery transition occurs. -/
theorem failover_retry_run : CrashStopReachable cfg 0 s15 := by
  have h1 : CrashStopReachable cfg 0 s1 := .step .init
    (.vote s0 0 1 42 (by decide) (by simp [s0, Protocol.initial])) (by decide)
  have evidence : Justified cfg.quorum s1.ballots (1, 42, false) :=
    ⟨[0], by decide, by decide, by decide⟩
  have h2 : CrashStopReachable cfg 0 s2 := .step h1
    (.select s1 0 1 42 false (by decide) (by decide)
      (by simp [Selected, s1, s0, Protocol.initial]) evidence (by decide)) (by decide)
  have h3 : CrashStopReachable cfg 0 s3 := .step h2
    (.dispatch s2 0 1 (by decide) (by decide) ⟨42, false, by decide⟩
      (by simp [s2, s1, s0, Protocol.initial]) (by simp [cfg])) (by decide)
  have h4 : CrashStopReachable cfg 0 s4 := .step h3
    (.respond s3 0 1 7 ⟨some 0, by decide⟩ (by simp [s3, s2, s1, s0, Protocol.initial])) (by decide)
  have h5 : CrashStopReachable cfg 0 s5 := .step h4
    (.propose s4 0 1 7 (by decide) (by decide) (by decide) (by decide)) (by decide)
  have h6 : CrashStopReachable cfg 0 s6 := .step h5
    (.crash s5 0 (by decide) (by decide)) (by decide)
  have h7 : CrashStopReachable cfg 0 s7 := .step h6
    (.elect s6 1 (by decide) (by decide) (by decide)) (by decide)
  have h8 : CrashStopReachable cfg 0 s8 := .step h7
    (.dispatch s7 1 1 (by decide) (by decide) ⟨42, false, by decide⟩
      (by simp [s7, s6, s5, s4, s3]) (by simp [cfg])) (by decide)
  have h9 : CrashStopReachable cfg 0 s9 := .step h8
    (.respond s8 1 1 9 ⟨some 1, by decide⟩ (by simp [s8, s7, s6, s5, s4])) (by decide)
  have h10 : CrashStopReachable cfg 0 s10 := .step h9
    (.propose s9 1 1 9 (by decide) (by decide) (by decide) (by decide)) (by decide)
  have h11 : CrashStopReachable cfg 0 s11 := .step h10
    (.decide s10 batch (by
      intro item hi
      have eq : item = (1, 9) := by simpa [batch] using hi
      subst item
      exact List.mem_cons_self)) (by decide)
  have h12 : CrashStopReachable cfg 0 s12 := .step h11
    (.learn s11 1 0 (by decide) (by decide)) (by decide)
  have h13 : CrashStopReachable cfg 0 s13 := .step h12
    (.process s12 1 batch (by decide) (by decide) (by decide)) (by decide)
  have h14 : CrashStopReachable cfg 0 s14 := .step h13
    (.learn s13 2 0 (by decide) (by decide)) (by decide)
  exact .step h14 (.process s14 2 batch (by decide) (by decide) (by decide)) (by decide)

theorem only_survivors_deliver :
    (s15.core.replica 0).delivered = [] ∧
    (s15.core.replica 1).delivered = [(1, 9)] ∧
    (s15.core.replica 2).delivered = [(1, 9)] ∧ s15.up 0 = false := by decide

theorem old_proposal_may_remain_uncommitted :
    (1, 7) ∈ s15.proposed ∧ (1, 7) ∉ s15.core.log.flatten := by decide

theorem retry_can_repeat_external_execution :
    s15.dispatches.length = 2 ∧ ¬ (s15.dispatches.map fun d => d.2.1).Nodup := by decide

theorem failed_node_cannot_rejoin : ¬ StaysDown s15
    { s15 with up := fun r => if r = 0 then true else s15.up r } := by decide

/-- The crash-stop paper premises are jointly satisfiable, without reviving the
failed node or requiring its pending proposal to commit. -/
theorem crash_stop_contracts_satisfiable : ∃ (tr : Nat → S) (finish : Nat),
    CrashStopBehavior cfg 0 tr ∧ StableLeader tr 1 finish ∧
    (∃ sender payload, (sender, 1, payload) ∈ (tr finish).ballots) ∧
    PendingHandlers cfg tr 1 1 ∧ StableConsensusProgress tr 1 finish ∧
    NonFaulty tr 1 ∧ NonFaulty tr 2 ∧
    (∀ t, finish ≤ t → (tr t).up 0 = false) ∧
    (∀ r, NonFaulty tr r → DeliveryProgress (fun t => (tr t).core) r) ∧
    (∀ t, finish ≤ t → (1, 7) ∉ (tr t).core.log.flatten) := by
  obtain ⟨tr, b, finish, steady⟩ := failover_retry_run.extend
  have stable : StableLeader tr 1 finish := by
    intro t ht; rw [steady t ht]; decide
  have healthy1 : NonFaulty tr 1 := b.stable_leader_nonfaulty finish stable
  have healthy2 : NonFaulty tr 2 := b.nonfaulty_of_eventually_up 2 finish (by
    intro t ht; rw [steady t ht]; decide)
  have handlers : PendingHandlers cfg tr 1 1 := by
    have impossible : ∀ start, ¬ (∀ t, start ≤ t → ¬ Agreed (tr t) 1) := by
      intro start notAgreed
      have h := notAgreed (max start finish) (Nat.le_max_left _ _)
      rw [steady _ (Nat.le_max_right _ _)] at h
      exact h (by unfold Agreed; decide)
    constructor
    · intro start enabled; exact False.elim (impossible start (fun t ht => (enabled t ht).2))
    · intro start enabled; exact False.elim (impossible start (fun t ht => (enabled t ht).2))
    · intro start enabled; exact False.elim (impossible start (fun t ht => (enabled t ht).2))
    · intro start enabled
      exact False.elim (impossible start (fun t ht => (enabled t ht).2.2.2))
  have consensus : StableConsensusProgress tr 1 finish := by
    intro t ht item attempt
    have lengths := congrArg List.length attempt.2.2
    rw [steady t ht, steady (t+1) (by omega)] at lengths
    simp at lengths
  have delivery : ∀ r, NonFaulty tr r → DeliveryProgress (fun t => (tr t).core) r := by
    intro r live
    have notZero : r ≠ 0 := by
      intro eq; subst r
      have hu := live finish
      rw [steady finish (Nat.le_refl _)] at hu
      contradiction
    have final : (s15.core.replica r).processed = 1 ∧ 0 ∈ (s15.core.replica r).learned := by
      have all : ∀ n : Node, n ≠ 0 →
          (s15.core.replica n).processed = 1 ∧ 0 ∈ (s15.core.replica n).learned := by decide
      exact all r notZero
    constructor
    · intro start slot hs
      let t := max start finish
      have bound := (b.protocol.core.log_mono (Nat.le_max_left start finish)).length_le
      change (tr start).core.log.length ≤ (tr t).core.log.length at bound
      rw [steady t (Nat.le_max_right _ _)] at bound
      have len : s15.core.log.length = 1 := by decide
      rw [len] at bound
      have zero : slot = 0 := by omega
      refine ⟨t, Nat.le_max_left _ _, ?_⟩
      change slot ∈ ((tr t).core.replica r).learned
      rw [steady t (Nat.le_max_right _ _), zero]
      exact final.2
    · intro start enabled
      have en := enabled (max start finish) (Nat.le_max_left _ _)
      change ((tr (max start finish)).core.replica r).processed <
        (tr (max start finish)).core.log.length ∧ _ at en
      rw [steady _ (Nat.le_max_right _ _), final.1] at en
      have len : s15.core.log.length = 1 := by decide
      rw [len] at en
      omega
  refine ⟨tr, finish, b, stable, ?_, handlers, consensus, healthy1, healthy2, ?_, delivery, ?_⟩
  · rw [steady finish (Nat.le_refl _)]; exact ⟨0, 42, by decide⟩
  · intro t ht; rw [steady t ht]; decide
  · intro t ht; rw [steady t ht]; exact old_proposal_may_remain_uncommitted.2

end Resdet.Paper.CrashStopTests
