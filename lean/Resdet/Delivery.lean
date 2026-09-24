import Std

/-!
Incremental duplicate suppression and its reference specification.
Only request IDs require decidable equality. Responses are arbitrary values.
-/
namespace Resdet

abbrev Item (Request Response : Type) := Request × Response

variable {Request Response : Type} [DecidableEq Request]

/-- An executable batch handler: append a response only if its ID is unseen.
The seen set is derived from the delivery history in this first prototype. -/
def applyItems : List (Item Request Response) → List (Item Request Response) →
    List (Item Request Response)
  | [], output => output
  | item :: rest, output =>
      if item.1 ∈ output.map Prod.fst then applyItems rest output
      else applyItems rest (output ++ [item])

/-- Independent reference scan, retaining the first occurrence of each ID. -/
def dedupFrom (seen : List Request) : List (Item Request Response) →
    List (Item Request Response)
  | [] => []
  | item :: rest =>
      if item.1 ∈ seen then dedupFrom seen rest
      else item :: dedupFrom (seen ++ [item.1]) rest

def dedup (items : List (Item Request Response)) := dedupFrom [] items

theorem applyItems_eq_reference (items output : List (Item Request Response)) :
    applyItems items output = output ++ dedupFrom (output.map Prod.fst) items := by
  induction items generalizing output with
  | nil => simp [applyItems, dedupFrom]
  | cons item rest ih =>
      simp only [applyItems, dedupFrom]
      split
      · exact ih output
      · rw [ih]
        simp [List.map_append, List.append_assoc]

theorem dedup_eq_applyItems (items : List (Item Request Response)) :
    dedup items = applyItems items [] := by
  simp [applyItems_eq_reference, dedup]

theorem applyItems_append (xs ys output : List (Item Request Response)) :
    applyItems (xs ++ ys) output = applyItems ys (applyItems xs output) := by
  induction xs generalizing output with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.cons_append, applyItems]
      split <;> apply ih

theorem output_prefix_applyItems (items output : List (Item Request Response)) :
    output <+: applyItems items output := by
  rw [applyItems_eq_reference]
  exact List.prefix_append _ _

theorem dedup_prefix {xs ys : List (Item Request Response)} (h : xs <+: ys) :
    dedup xs <+: dedup ys := by
  obtain ⟨suffix, rfl⟩ := h
  simp only [dedup_eq_applyItems, applyItems_append]
  exact output_prefix_applyItems _ _

theorem applyItems_nodup (items output : List (Item Request Response))
    (h : (output.map Prod.fst).Nodup) :
    ((applyItems items output).map Prod.fst).Nodup := by
  induction items generalizing output with
  | nil => exact h
  | cons item rest ih =>
      simp only [applyItems]
      split
      · exact ih output h
      · rename_i unseen
        apply ih
        simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
        refine ⟨h, by simp, ?_⟩
        intro a ha b hb hab
        have hb' : b = item.1 := by simpa using hb
        exact unseen ((hab.trans hb') ▸ ha)

theorem dedup_nodup (items : List (Item Request Response)) :
    ((dedup items).map Prod.fst).Nodup := by
  rw [dedup_eq_applyItems]
  exact applyItems_nodup items [] (by simp)

theorem applyItems_mem {item : Item Request Response}
    (items output : List (Item Request Response))
    (h : item ∈ applyItems items output) : item ∈ output ∨ item ∈ items := by
  induction items generalizing output with
  | nil => exact Or.inl h
  | cons next rest ih =>
      simp only [applyItems] at h
      split at h
      · rcases ih output h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases ih (output ++ [next]) h with h | h
        · simp only [List.mem_append, List.mem_singleton] at h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (by simp [h])
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem dedup_mem {item : Item Request Response} {items : List (Item Request Response)}
    (h : item ∈ dedup items) : item ∈ items := by
  rw [dedup_eq_applyItems] at h
  simpa using applyItems_mem items [] h

omit [DecidableEq Request] in
/-- Within an ID-unique history, equal IDs identify the same response item. -/
theorem eq_of_same_id {items : List (Item Request Response)}
    (unique : (items.map Prod.fst).Nodup)
    {a b : Item Request Response} (ha : a ∈ items) (hb : b ∈ items)
    (ids : a.1 = b.1) : a = b := by
  induction items with
  | nil => simp at ha
  | cons first rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · rfl
        · exact False.elim (unique.1 (ids ▸ List.mem_map_of_mem hb))
      · rcases hb with rfl | hb
        · exact False.elim (unique.1 (ids ▸ List.mem_map_of_mem ha))
        · exact ih unique.2 ha hb

end Resdet
