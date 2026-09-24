import Resdet.ProtocolSafety

namespace Resdet

/-- Weak fairness: continuous enabling eventually produces an occurrence.
This is not a bounded timeout assumption. -/
def WeakFair (enabled occurs : Nat → Prop) : Prop :=
  ∀ start, (∀ time, start ≤ time → enabled time) →
    ∃ time, start ≤ time ∧ occurs time

def EventuallyFrom (start : Nat) (p : Nat → Prop) := ∃ time, start ≤ time ∧ p time

theorem propagate {p : Nat → Prop} (next : ∀ n, p n → p (n + 1))
    {a b : Nat} (hab : a ≤ b) (ha : p a) : p b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simpa using ha
  | succ d ih => simpa [Nat.add_assoc] using next (a + d) ih

/-- A general temporal progress rule: fairness plus a persistent precondition.
The postcondition is proved using an action's effect, not assumed eventual. -/
theorem fair_progress {p q enabled occurs : Nat → Prop} {start : Nat}
    (persistent : ∀ a b, a ≤ b → p a → p b)
    (enable : ∀ t, start ≤ t → p t → ¬ q t → enabled t)
    (effect : ∀ t, start ≤ t → occurs t → q (t + 1))
    (fair : WeakFair enabled occurs) (hp : p start) : EventuallyFrom start q := by
  classical
  apply Classical.byContradiction
  intro hn
  have noQ : ∀ t, start ≤ t → ¬ q t := by
    intro t ht hq
    exact hn ⟨t, ht, hq⟩
  obtain ⟨t, ht, action⟩ := fair start (fun t ht => enable t ht
    (persistent start t ht hp) (noQ t ht))
  exact noQ (t + 1) (by omega) (effect t ht action)

variable {Node Request Response : Type} [DecidableEq Node] [DecidableEq Request]

structure Behavior (trace : Nat → State Node Request Response) : Prop where
  init : trace 0 = initial
  next : ∀ t, Step (trace t) (trace (t + 1))

theorem Behavior.reachable {tr : Nat → State Node Request Response} (b : Behavior tr) (t) :
    Reachable (tr t) := by
  induction t with
  | zero => rw [b.init]; exact .init
  | succ t ih => exact .step ih (b.next t)

theorem step_processed_mono {s t : State Node Request Response} (h : Step s t) (r : Node) :
    (s.replica r).processed ≤ (t.replica r).processed := by
  cases h with
  | process n batch _ _ => by_cases hn : r = n <;> simp [processBatch, hn]
  | learn n slot _ => by_cases hn : r = n <;> simp [learnSlot, hn]
  | _ => exact Nat.le_refl _

theorem step_learned_mono {s t : State Node Request Response} (h : Step s t) (r : Node) :
    (s.replica r).learned ⊆ (t.replica r).learned := by
  cases h with
  | process n batch _ _ => by_cases hn : r = n <;> simp [processBatch, hn]
  | learn n slot _ =>
      by_cases hn : r = n
      · simp [learnSlot, hn]
      · simp [learnSlot, hn]
  | _ => exact fun _ h => h

theorem step_log_mono {s t : State Node Request Response} (h : Step s t) : s.log <+: t.log := by
  cases h with
  | append => exact List.prefix_append _ _
  | _ => exact List.prefix_refl _

theorem Behavior.processed_mono {tr : Nat → State Node Request Response} (b : Behavior tr)
    (r : Node) {a c : Nat} (h : a ≤ c) : ((tr a).replica r).processed ≤
      ((tr c).replica r).processed := by
  apply propagate (p := fun t => ((tr a).replica r).processed ≤ ((tr t).replica r).processed)
    (fun t ht => Nat.le_trans ht (step_processed_mono (b.next t) r)) h (Nat.le_refl _)

theorem Behavior.learned_mono {tr : Nat → State Node Request Response} (b : Behavior tr)
    (r : Node) {a c : Nat} (h : a ≤ c) : ((tr a).replica r).learned ⊆
      ((tr c).replica r).learned := by
  intro slot hs
  exact propagate (fun t ht => step_learned_mono (b.next t) r ht) h hs

theorem Behavior.log_mono {tr : Nat → State Node Request Response} (b : Behavior tr)
    {a c : Nat} (h : a ≤ c) : (tr a).log <+: (tr c).log := by
  exact propagate (p := fun t => (tr a).log <+: (tr t).log)
    (fun t ht => ht.trans (step_log_mono (b.next t))) h (List.prefix_refl _)

/-- CG3 learning and L4 local processing for one non-faulty replica.
Neither field assumes eventual processing of an entire prefix or delivery. -/
structure DeliveryProgress (tr : Nat → State Node Request Response) (r : Node) : Prop where
  learn : ∀ start slot, slot < (tr start).log.length →
    EventuallyFrom start (fun t => slot ∈ ((tr t).replica r).learned)
  process : WeakFair
    (fun t => ((tr t).replica r).processed < (tr t).log.length ∧
      ((tr t).replica r).processed ∈ ((tr t).replica r).learned)
    (fun t => ((tr (t + 1)).replica r).processed = ((tr t).replica r).processed + 1)

theorem eventually_processed {tr : Nat → State Node Request Response} (b : Behavior tr)
    (r : Node) (progress : DeliveryProgress tr r) (count start : Nat)
    (decided : count ≤ (tr start).log.length) :
    EventuallyFrom start (fun t => count ≤ ((tr t).replica r).processed) := by
  induction count with
  | zero => exact ⟨start, Nat.le_refl _, Nat.zero_le _⟩
  | succ k ih =>
      obtain ⟨u, hu, processed⟩ := ih (by omega)
      have logBound := (b.log_mono hu).length_le
      obtain ⟨v, hv, learned⟩ := progress.learn u k (by omega)
      have advance : EventuallyFrom v (fun t => k + 1 ≤ ((tr t).replica r).processed) := by
        apply fair_progress
          (p := fun t => k ≤ ((tr t).replica r).processed ∧
            k ∈ ((tr t).replica r).learned ∧ k < (tr t).log.length)
          (enabled := fun t => ((tr t).replica r).processed < (tr t).log.length ∧
            ((tr t).replica r).processed ∈ ((tr t).replica r).learned)
          (occurs := fun t => ((tr (t+1)).replica r).processed = ((tr t).replica r).processed + 1)
        · intro a c hac hp
          exact ⟨Nat.le_trans hp.1 (b.processed_mono r hac),
            b.learned_mono r hac hp.2.1, Nat.lt_of_lt_of_le hp.2.2 (b.log_mono hac).length_le⟩
        · intro t _ hp hq
          have eq : ((tr t).replica r).processed = k := by omega
          simpa [eq] using And.intro hp.2.2 hp.2.1
        · intro t ht action
          have := b.processed_mono r (Nat.le_trans hv ht)
          omega
        · exact progress.process
        · exact ⟨Nat.le_trans processed (b.processed_mono r hv), learned,
            Nat.lt_of_lt_of_le (by omega) (b.log_mono hv).length_le⟩
      obtain ⟨w, hw, done⟩ := advance
      exact ⟨w, Nat.le_trans hu (Nat.le_trans hv hw), done⟩

/-- A committed request eventually reaches a non-faulty replica. -/
theorem agreed_eventually_delivered {tr : Nat → State Node Request Response} (b : Behavior tr)
    (r : Node) (progress : DeliveryProgress tr r) (start : Nat) {request : Request}
    (agreed : request ∈ (tr start).log.flatten.map Prod.fst) :
    EventuallyFrom start (fun t => ∃ value, (request, value) ∈ ((tr t).replica r).delivered) := by
  obtain ⟨t, ht, hp⟩ := eventually_processed b r progress (tr start).log.length start (Nat.le_refl _)
  have inv := reachable_invariant (b.reachable t)
  have pre : (tr start).log <+: (tr t).log.take ((tr t).replica r).processed :=
    List.prefix_of_prefix_length_le (b.log_mono ht) (List.take_prefix _ _) (by
      simp only [List.length_take]
      have := inv.processedWithinLog r
      omega)
  have covered := dedup_covers ((flatten_prefix pre).map Prod.fst |>.subset agreed)
  rw [← inv.appliedPrefixCorrect r] at covered
  obtain ⟨⟨id, value⟩, hm, heq⟩ := List.mem_map.mp covered
  exact ⟨t, ht, value, by simpa using heq ▸ hm⟩

end Resdet
