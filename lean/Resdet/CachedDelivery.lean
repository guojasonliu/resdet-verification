import Resdet.Safety

namespace Resdet

variable {Request Response : Type} [DecidableEq Request]

/-- A separately stored seen cache, as in the protocol rather than the core. -/
def applyCached : List (Item Request Response) → List Request →
    List (Item Request Response) → List Request × List (Item Request Response)
  | [], seen, output => (seen, output)
  | item :: rest, seen, output =>
      if item.1 ∈ seen then applyCached rest seen output
      else applyCached rest (seen ++ [item.1]) (output ++ [item])

theorem applyCached_correct (items : List (Item Request Response)) (seen : List Request)
    (output : List (Item Request Response)) (coherent : seen = output.map Prod.fst) :
    applyCached items seen output =
      ((applyItems items output).map Prod.fst, applyItems items output) := by
  subst seen
  induction items generalizing output with
  | nil => rfl
  | cons item rest ih =>
      simp only [applyCached, applyItems]
      split
      · exact ih output
      · simpa using ih (output ++ [item])

/-- Every input ID is represented in the output, possibly by an earlier value. -/
theorem applyItems_covers (items output : List (Item Request Response)) :
    ∀ request, request ∈ output.map Prod.fst ∨ request ∈ items.map Prod.fst →
      request ∈ (applyItems items output).map Prod.fst := by
  induction items generalizing output with
  | nil => simp [applyItems]
  | cons item rest ih =>
      intro request h
      simp only [applyItems]
      split
      · rename_i seen
        apply ih
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | rfl | h
        · exact Or.inl h
        · exact Or.inl seen
        · exact Or.inr h
      · apply ih
        simpa only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false, or_assoc] using h

theorem dedup_covers {items : List (Item Request Response)} {request : Request}
    (h : request ∈ items.map Prod.fst) : request ∈ (dedup items).map Prod.fst := by
  rw [dedup_eq_applyItems]
  exact applyItems_covers items [] request (Or.inr h)

end Resdet
