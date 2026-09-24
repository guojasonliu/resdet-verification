import Resdet

namespace Resdet.Protocol.Tests

abbrev S := State Bool Nat Nat Nat
def cfg : Config := ⟨1, by decide, true, false⟩
def p0 : S := initial false
def p1 := { p0 with ballots := [(false, 1, 42)] }
def p2 := { p1 with choices := [(1, 42, false)] }
def p3 := { p2 with dispatches := [(false, 1, some false)] }
def p4 := { p3 with executions := [(false, 1, 7)], observed := [(1, 7)] }
def p5 := { p4 with proposed := [(1, 7)] }
def p6 := { p5 with up := fun r => if r = false then false else p5.up r, leader := none }
def p7 := { p6 with leader := some true }
def p8 := { p7 with dispatches := (true, 1, some true) :: p7.dispatches }
def p9 := { p8 with
  executions := (true, 1, 9) :: p8.executions
  observed := (1, 9) :: p8.observed }
def p10 := { p9 with proposed := (1, 9) :: p9.proposed }
-- Consensus can order the second physical result first.
def batch : List (Item Nat Nat) := [(1, 9), (1, 7)]
def p11 := { p10 with core := appendBatch p10.core batch }
def p12 := { p11 with core := learnSlot p11.core true 0 }
def p13 := process p12 true batch
def p14 := { p13 with up := fun r => if r = false then true else p13.up r }
def p15 := { p14 with core := learnSlot p14.core false 0 }
def p16 := process p15 false batch

theorem recovery_run : Reachable cfg false p16 := by
  have h1 : Reachable cfg false p1 := .step .init (.vote p0 false 1 42 (by decide) (by simp [p0, initial]))
  have evidence : Justified cfg.quorum p1.ballots (1, 42, false) := by
    exact ⟨[false], by decide, by decide, by decide⟩
  have selected : Selected p2 1 := ⟨42, false, by decide⟩
  have h2 : Reachable cfg false p2 := .step h1 (.select p1 false 1 42 false
    (by decide) (by decide) (by simp [Selected, p1, p0, initial]) evidence (by decide))
  have h3 : Reachable cfg false p3 := .step h2 (.dispatch p2 false 1 (by decide) (by decide)
    selected (by simp [p2, p1, p0, initial]) (by simp [cfg]))
  have h4 : Reachable cfg false p4 := .step h3 (.respond p3 false 1 7 ⟨some false, by decide⟩
    (by simp [p3, p2, p1, p0, initial]))
  have h5 : Reachable cfg false p5 := .step h4 (.propose p4 false 1 7 (by decide) (by decide)
    (by decide) (by decide))
  have h6 : Reachable cfg false p6 := .step h5 (.crash p5 false (by decide) (by decide))
  have h7 : Reachable cfg false p7 := .step h6 (.elect p6 true (by decide) (by decide) (by decide))
  have h8 : Reachable cfg false p8 := .step h7 (.dispatch p7 true 1 (by decide) (by decide)
    ⟨42, false, by decide⟩ (by simp [p7, p6, p5, p4, p3]) (by simp [cfg]))
  have h9 : Reachable cfg false p9 := .step h8 (.respond p8 true 1 9 ⟨some true, by decide⟩
    (by simp [p8, p7, p6, p5, p4]))
  have h10 : Reachable cfg false p10 := .step h9 (.propose p9 true 1 9
    (by decide) (by decide) (by decide) (by decide))
  have h11 : Reachable cfg false p11 := .step h10 (.decide p10 batch (by
    intro item hi
    simpa [batch, p10, p9, p8, p7, p6, p5] using hi))
  have h12 : Reachable cfg false p12 := .step h11 (.learn p11 true 0 (by decide) (by decide))
  have h13 : Reachable cfg false p13 := .step h12 (.process p12 true batch
    (by decide) (by decide) (by decide))
  have h14 : Reachable cfg false p14 := .step h13 (.recover p13 false (by decide) (by decide))
  have h15 : Reachable cfg false p15 := .step h14 (.learn p14 false 0 (by decide) (by decide))
  exact .step h15 (.process p15 false batch (by decide) (by decide) (by decide))

theorem recovered_replicas_agree :
    (p16.core.replica false).delivered = [(1, 9)] ∧
    (p16.core.replica true).delivered = [(1, 9)] ∧ p16.seen false = [1] ∧
    p16.seen true = [1] := by decide

theorem physical_execution_can_repeat : p16.dispatches.length = 2 ∧
    ¬ (p16.dispatches.map fun d => d.2.1).Nodup := by decide

theorem reproposal_reachable : Reachable cfg false
    { p16 with proposed := (1, 9) :: p16.proposed } :=
  .step recovery_run (.repropose p16 true 1 9 (by decide) (by decide) (by decide) (by decide))

theorem two_distinct_matching_voters :
    Justified 2 [(false, 1, 42), (true, 1, 42)] (1, 42, false) :=
  ⟨[false, true], by decide, by decide, by decide⟩

theorem invalid_double_counting : ¬ ([false, false] : List Bool).Nodup := by decide

def fallbackCfg : Config := ⟨2, by decide, false, true⟩
def f0 : S := initial false
def f1 := { f0 with ballots := [(false, 1, 42)] }
def f2 := { f1 with choices := [(1, 42, true)] }

theorem fallback_run : Reachable fallbackCfg false f2 := by
  have h1 : Reachable fallbackCfg false f1 := .step .init (.vote f0 false 1 42
    (by decide) (by simp [f0, initial]))
  exact .step h1 (.select f1 false 1 42 true (by decide) (by decide)
    (by simp [Selected, f1, f0, initial]) ⟨false, by decide⟩ (by decide))

theorem fallback_is_marked : (1, 42, true) ∈ f2.choices := by decide

-- A valid infinite core execution which learns but never processes.
def waiting0 : Resdet.State Bool Nat Nat := Resdet.initial
def waiting1 := appendBatch waiting0 [(1, 7)]
def waiting2 := learnSlot waiting1 false 0
def waitingTrace : Nat → Resdet.State Bool Nat Nat
  | 0 => waiting0
  | 1 => waiting1
  | _ + 2 => waiting2

theorem waiting_behavior : Resdet.Behavior waitingTrace := by
  constructor
  · rfl
  · intro t
    cases t with
    | zero => exact .append _ [(1, 7)]
    | succ t =>
        cases t with
        | zero => exact .learn _ false 0 (by decide)
        | succ t => exact .stutter _

theorem waiting_never_delivers (t : Nat) : (waitingTrace t |>.replica false).delivered = [] := by
  cases t with
  | zero => rfl
  | succ t => cases t <;> rfl

theorem fairness_is_necessary : ¬ DeliveryProgress waitingTrace false := by
  intro progress
  obtain ⟨t, _, value, delivered⟩ := agreed_eventually_delivered waiting_behavior false
    progress 1 (request := 1) (by decide)
  rw [waiting_never_delivers] at delivered
  simp at delivered

/-- Any finite reachable execution extends to a behavior which then stutters. -/
theorem extend_run {s : S} (h : Reachable cfg false s) :
    ∃ tr : Nat → S, Behavior cfg false tr ∧ ∃ finish, ∀ t, finish ≤ t → tr t = s := by
  induction h with
  | init => exact ⟨fun _ => initial false, ⟨rfl, fun _ => .stutter _⟩, 0, fun _ _ => rfl⟩
  | @step s t _ step ih =>
      obtain ⟨tr, b, finish, steady⟩ := ih
      let tr' := fun k => if k ≤ finish then tr k else t
      refine ⟨tr', ?_, finish + 1, ?_⟩
      · constructor
        · simpa [tr'] using b.init
        · intro k
          by_cases before : k < finish
          · simpa [tr', show k ≤ finish by omega, show k + 1 ≤ finish by omega] using b.next k
          · by_cases atEnd : k = finish
            · subst k
              simpa [tr', steady finish (Nat.le_refl _), show ¬ finish + 1 ≤ finish by omega] using step
            · simpa [tr', show ¬ k ≤ finish by omega, show ¬ k + 1 ≤ finish by omega]
                using Step.stutter (cfg := cfg) t
      · intro k hk
        simp [tr', show ¬ k ≤ finish by omega]

theorem fair_if_eventually_always {enabled occurs : Nat → Prop} (finish : Nat)
    (steady : ∀ t, finish ≤ t → occurs t) : WeakFair enabled occurs := by
  intro start _
  exact ⟨max start finish, Nat.le_max_left _ _, steady _ (Nat.le_max_right _ _)⟩

/-- Non-vacuity: one behavior jointly satisfies every liveness contract for
request 1 and both replicas, even after the two-leader crash/recovery prefix. -/
theorem progress_contracts_satisfiable : ∃ (tr : Nat → S) (finish : Nat),
    Behavior cfg false tr ∧ StableLeader tr true finish ∧ GateReady cfg (tr finish) 1 ∧
    LocalProgress cfg tr true 1 ∧ ConsensusProgress tr ∧
    ∀ r, DeliveryProgress (fun t => (tr t).core) r := by
  obtain ⟨tr, b, finish, steady⟩ := extend_run recovery_run
  have stable : StableLeader tr true finish := by
    intro t ht
    rw [steady t ht]
    decide
  have ready : GateReady cfg (tr finish) 1 := by
    rw [steady finish (Nat.le_refl _)]
    exact ⟨42, false, ⟨[false], by decide, by decide, by decide⟩, by decide⟩
  have localP : LocalProgress cfg tr true 1 := by
    constructor
    · apply fair_if_eventually_always finish
      intro t ht
      rw [steady (t+1) (by omega)]
      exact ⟨42, false, by decide⟩
    · apply fair_if_eventually_always finish
      intro t ht
      rw [steady (t+1) (by omega)]
      exact ⟨some true, by decide⟩
    · apply fair_if_eventually_always finish
      intro t ht
      rw [steady (t+1) (by omega)]
      exact ⟨9, by decide⟩
    · apply fair_if_eventually_always finish
      intro t ht
      rw [steady (t+1) (by omega)]
      exact ⟨9, by decide⟩
  have consensus : ConsensusProgress tr := by
    intro start item hi
    let t := max start finish
    have sub : (tr start).proposed ⊆ (tr t).proposed :=
      propagate (p := fun u => (tr start).proposed ⊆ (tr u).proposed)
        (fun u hs _ hm => proposals_step_mono (b.next u) (hs hm))
        (Nat.le_max_left _ _) (fun _ h => h)
    have itemFinal : item ∈ p16.proposed := by
      rw [← steady t (Nat.le_max_right _ _)]
      exact sub hi
    refine ⟨t, Nat.le_max_left _ _, ?_⟩
    change item ∈ (tr t).core.log.flatten
    rw [steady t (Nat.le_max_right _ _)]
    exact (show p16.proposed = p16.core.log.flatten from by decide) ▸ itemFinal
  refine ⟨tr, finish, b, stable, ready, localP, consensus, ?_⟩
  intro r
  constructor
  · intro start slot hs
    let t := max start finish
    have bound := (b.core.log_mono (Nat.le_max_left start finish)).length_le
    change (tr start).core.log.length ≤ (tr t).core.log.length at bound
    rw [steady t (Nat.le_max_right _ _)] at bound
    have len : p16.core.log.length = 1 := by decide
    rw [len] at bound
    have eq : slot = 0 := by omega
    refine ⟨t, Nat.le_max_left _ _, ?_⟩
    change slot ∈ ((tr t).core.replica r).learned
    rw [steady t (Nat.le_max_right _ _), eq]
    cases r <;> decide
  · intro start enabled
    have en := enabled (max start finish) (Nat.le_max_left _ _)
    change ((tr (max start finish)).core.replica r).processed <
      (tr (max start finish)).core.log.length ∧ _ at en
    rw [steady _ (Nat.le_max_right _ _)] at en
    have impossible : ¬ (p16.core.replica r).processed < p16.core.log.length := by
      cases r <;> decide
    exact False.elim (impossible en.1)

/-- The weaker stable-leader consensus version also has jointly satisfiable
premises, not only the global-buffer version. -/
theorem retry_contracts_satisfiable : ∃ (tr : Nat → S) (finish : Nat),
    Behavior cfg false tr ∧ StableLeader tr true finish ∧ GateReady cfg (tr finish) 1 ∧
    RetryProgress cfg tr true 1 ∧ StableConsensusProgress tr true finish ∧
    ∀ r, DeliveryProgress (fun t => (tr t).core) r := by
  obtain ⟨tr, finish, b, stable, ready, localP, consensus, delivery⟩ := progress_contracts_satisfiable
  have ingress : EventuallyFrom 0 (fun t => GateReady cfg (tr t) 1) :=
    ⟨finish, Nat.zero_le _, ready⟩
  obtain ⟨d, _, value, delivered⟩ := eventual_delivery b finish stable 1 ingress localP consensus
    false (delivery false)
  have agreedAtD : Agreed (tr d) 1 := List.mem_map_of_mem
    (Resdet.delivered_in_log (reachable_refines (b.reachable d)) false delivered)
  have retry : RetryProgress cfg tr true 1 := by
    refine ⟨localP.select, localP.dispatch, localP.respond, ?_⟩
    intro start enabled
    let t := max start d
    have en := enabled t (Nat.le_max_left _ _)
    have agreed : Agreed (tr t) 1 :=
      ((Resdet.flatten_prefix (b.core.log_mono (Nat.le_max_right start d))).map Prod.fst).subset agreedAtD
    exact False.elim (en.2.2.2 agreed)
  have stableCG : StableConsensusProgress tr true finish := by
    intro t _ item attempt
    have proposed : item ∈ (tr (t+1)).proposed := by
      rw [attempt.2.2]
      exact List.mem_cons_self
    obtain ⟨u, hu, agreed⟩ := consensus (t+1) item proposed
    exact ⟨u, by omega, agreed⟩
  exact ⟨tr, finish, b, stable, ready, retry, stableCG, delivery⟩

end Resdet.Protocol.Tests
