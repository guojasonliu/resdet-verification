import Resdet.Model

namespace Resdet

variable {Node Request Response : Type} [DecidableEq Node] [DecidableEq Request]

omit [DecidableEq Node] [DecidableEq Request] in
theorem flatten_prefix {xs ys : List (List (Item Request Response))}
    (h : xs <+: ys) : xs.flatten <+: ys.flatten := by
  obtain ⟨suffix, rfl⟩ := h
  rw [List.flatten_append]
  exact List.prefix_append _ _

/-- Each independent replica history is a prefix of one canonical history. -/
theorem delivered_prefix {s : State Node Request Response} (h : Reachable s) (r : Node) :
    (s.replica r).delivered <+: dedup s.log.flatten := by
  rw [(reachable_invariant h).appliedPrefixCorrect r]
  exact dedup_prefix (flatten_prefix (List.take_prefix _ _))

/-- At-most-once workflow delivery, even if the log repeats or conflicts on IDs. -/
theorem at_most_once_delivery {s : State Node Request Response}
    (h : Reachable s) (r : Node) : ((s.replica r).delivered.map Prod.fst).Nodup := by
  rw [(reachable_invariant h).appliedPrefixCorrect r]
  exact dedup_nodup _

theorem delivery_count_le_one {s : State Node Request Response}
    (h : Reachable s) (r : Node) (request : Request) :
    ((s.replica r).delivered.map Prod.fst).count request ≤ 1 := by
  exact List.nodup_iff_count.mp (at_most_once_delivery h r) request

/-- Agreement is conditional on both replicas having delivered the request;
it does not assert eventual delivery. -/
theorem response_agreement {s : State Node Request Response} (h : Reachable s)
    (left right : Node) {request : Request} {a b : Response}
    (ha : (request, a) ∈ (s.replica left).delivered)
    (hb : (request, b) ∈ (s.replica right).delivered) : a = b := by
  have same := eq_of_same_id (dedup_nodup s.log.flatten)
    ((delivered_prefix h left).subset ha) ((delivered_prefix h right).subset hb) rfl
  exact congrArg Prod.snd same

theorem prefix_agreement {s : State Node Request Response} (h : Reachable s)
    (left right : Node) :
    (s.replica left).delivered <+: (s.replica right).delivered ∨
    (s.replica right).delivered <+: (s.replica left).delivered := by
  exact List.prefix_or_prefix_of_prefix (delivered_prefix h left) (delivered_prefix h right)

omit [DecidableEq Node] [DecidableEq Request] in
theorem heads_eq_of_prefix {xs ys : List (Item Request Response)} {a b : Item Request Response}
    (h : xs <+: ys) (hx : xs.head? = some a) (hy : ys.head? = some b) : a = b := by
  obtain ⟨suffix, rfl⟩ := h
  cases xs with
  | nil => simp at hx
  | cons first rest =>
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hx hy
      exact hx.symm.trans hy

/-- Agreement on the first response race, when both histories are nonempty. -/
theorem race_winner_agreement {s : State Node Request Response} (h : Reachable s)
    (left right : Node) {a b : Item Request Response}
    (ha : (s.replica left).delivered.head? = some a)
    (hb : (s.replica right).delivered.head? = some b) : a.1 = b.1 := by
  rcases prefix_agreement h left right with hp | hp
  · exact congrArg Prod.fst (heads_eq_of_prefix hp ha hb)
  · exact congrArg Prod.fst (heads_eq_of_prefix hp hb ha).symm

/-- Validity relative to the consensus log, not to physical execution. -/
theorem delivered_in_log {s : State Node Request Response} (h : Reachable s)
    (r : Node) {item : Item Request Response} (hi : item ∈ (s.replica r).delivered) :
    item ∈ s.log.flatten := by
  exact dedup_mem ((delivered_prefix h r).subset hi)

/-- No transition can retract or replace an already delivered response. -/
theorem step_delivery_monotone {s t : State Node Request Response} (h : Step s t)
    (r : Node) : (s.replica r).delivered <+: (t.replica r).delivered := by
  cases h with
  | append => exact List.prefix_refl _
  | stutter => exact List.prefix_refl _
  | learn node slot _ =>
      by_cases hn : r = node <;> simp [learnSlot, hn]
  | process node batch _ _ =>
      by_cases hn : r = node
      · simpa [processBatch, hn] using
          output_prefix_applyItems batch (s.replica node).delivered
      · simp [processBatch, hn]

end Resdet
