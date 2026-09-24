import Resdet.Protocol

namespace Resdet.Protocol

variable {Node Request Payload Response : Type}
variable [DecidableEq Node] [DecidableEq Request]
variable {cfg : Config} {leader : Node} {s t : State Node Request Payload Response}

omit [DecidableEq Node] [DecidableEq Request] in
theorem justified_mono {q : Nat} {a b : List (Ballot Node Request Payload)}
    {choice : Choice Request Payload} (sub : a ⊆ b) (h : Justified q a choice) :
    Justified q b choice := by
  unfold Justified at h ⊢
  split at h
  · rename_i flag
    rw [if_pos flag]
    obtain ⟨v, hv⟩ := h
    exact ⟨v, sub hv⟩
  · rename_i flag
    rw [if_neg flag]
    obtain ⟨vs, hn, hq, hv⟩ := h
    exact ⟨vs, hn, hq, fun v hm => sub (hv v hm)⟩

theorem step_choices_mono (h : Step cfg s t) : s.choices ⊆ t.choices := by
  cases h with
  | select => exact List.subset_cons_of_subset _ (fun _ h => h)
  | _ => exact fun _ h => h

theorem step_selected_mono (h : Step cfg s t) {request : Request}
    (hs : Selected s request) : Selected t request := by
  obtain ⟨p, f, hp⟩ := hs
  exact ⟨p, f, step_choices_mono h hp⟩

theorem selection_justified (h : Reachable cfg leader s) :
    ∀ choice ∈ s.choices, Justified cfg.quorum s.ballots choice := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | vote n request payload _ _ =>
          intro c hc
          exact justified_mono (List.subset_cons_of_subset _ (fun _ h => h)) (ih c hc)
      | select n request payload fallback _ _ _ evidence _ =>
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact evidence
          · exact ih c hc
      | _ => exact ih

theorem fallback_explicit (h : Reachable cfg leader s) :
    ∀ choice ∈ s.choices, choice.2.2 = true → cfg.timeoutFallback = true := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | select n request payload fallback _ _ _ _ allowed =>
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact allowed
          · exact ih c hc
      | _ => exact ih

theorem strict_quorum (h : Reachable cfg leader s) (strict : cfg.timeoutFallback = false)
    {choice : Choice Request Payload} (hc : choice ∈ s.choices) :
    choice.2.2 = false ∧ Justified cfg.quorum s.ballots choice := by
  constructor
  · have := fallback_explicit h choice hc
    cases he : choice.2.2 <;> simp_all
  · exact selection_justified h choice hc

/-- The event records the leader at dispatch time, not the current leader. -/
theorem only_leader_dispatches (h : Reachable cfg leader s) :
    ∀ d ∈ s.dispatches, d.2.2 = some d.1 := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | dispatch n request leader _ _ _ _ =>
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact leader
          · exact ih d hd
      | _ => exact ih

theorem no_dispatch_before_selection (h : Reachable cfg leader s) :
    ∀ d ∈ s.dispatches, Selected s d.2.1 := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | select =>
          intro d hd
          obtain ⟨p, f, hp⟩ := ih d hd
          exact ⟨p, f, List.mem_cons_of_mem _ hp⟩
      | dispatch n request _ _ selected _ _ =>
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact selected
          · exact ih d hd
      | _ => exact ih

theorem executions_dispatched (h : Reachable cfg leader s) :
    ∀ e ∈ s.executions, ∃ l, (e.1, e.2.1, l) ∈ s.dispatches := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | dispatch =>
          intro e he
          obtain ⟨l, hl⟩ := ih e he
          exact ⟨l, List.mem_cons_of_mem _ hl⟩
      | respond n request value dispatched _ =>
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact dispatched
          · exact ih e he
      | _ => exact ih

theorem executions_observed (h : Reachable cfg leader s) :
    ∀ e ∈ s.executions, (e.2.1, e.2.2) ∈ s.observed := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | respond =>
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih e he)
      | _ => exact ih

theorem observed_executed (h : Reachable cfg leader s) :
    ∀ item ∈ s.observed, ∃ n, (n, item.1, item.2) ∈ s.executions := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | respond n request value _ _ =>
          intro item hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact ⟨n, List.mem_cons_self⟩
          · obtain ⟨n, hn⟩ := ih item hi
            exact ⟨n, List.mem_cons_of_mem _ hn⟩
      | _ => exact ih

theorem proposal_validity (h : Reachable cfg leader s) : s.proposed ⊆ s.observed := by
  induction h with
  | init => simp [initial]
  | step reach step ih =>
      cases step with
      | respond => exact fun _ hm => List.mem_cons_of_mem _ (ih hm)
      | propose n request value _ _ executed _ =>
          intro item hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact executions_observed reach _ executed
          · exact ih hi
      | repropose n request value _ _ executed _ =>
          intro item hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact executions_observed reach _ executed
          · exact ih hi
      | _ => exact ih

theorem consensus_validity (h : Reachable cfg leader s) : s.core.log.flatten ⊆ s.proposed := by
  induction h with
  | init => simp [initial, Resdet.initial]
  | step _ step ih =>
      cases step with
      | propose => exact fun _ hm => List.mem_cons_of_mem _ (ih hm)
      | repropose => exact fun _ hm => List.mem_cons_of_mem _ (ih hm)
      | decide batch valid =>
          intro item hi
          simp only [appendBatch, List.flatten_append, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.mem_append] at hi
          exact hi.elim (fun hm => ih hm) (valid item)
      | _ => exact ih

theorem at_most_one_physical_dispatch (h : Reachable cfg leader s)
    (stable : cfg.crashes = false) : (s.dispatches.map fun d => d.2.1).Nodup := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | dispatch n request _ _ _ _ once =>
          simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, ih⟩
          intro hm
          obtain ⟨d, hd, he⟩ := List.mem_map.mp hm
          exact once stable d hd he
      | _ => exact ih

/-- Physical provenance and selection, in addition to core log validity. -/
theorem response_validity (h : Reachable cfg leader s) (r : Node)
    {item : Item Request Response} (hi : item ∈ (s.core.replica r).delivered) :
    item ∈ s.observed ∧ Selected s item.1 ∧
      ∃ n l, (n, item.1, item.2) ∈ s.executions ∧ (n, item.1, l) ∈ s.dispatches := by
  have observed := proposal_validity h (consensus_validity h
    (Resdet.delivered_in_log (reachable_refines h) r hi))
  obtain ⟨n, executed⟩ := observed_executed h item observed
  obtain ⟨l, dispatched⟩ := executions_dispatched h _ executed
  exact ⟨observed, no_dispatch_before_selection h _ dispatched, n, l, executed, dispatched⟩

theorem response_agreement (h : Reachable cfg leader s) (left right : Node)
    {request : Request} {a b : Response}
    (ha : (request, a) ∈ (s.core.replica left).delivered)
    (hb : (request, b) ∈ (s.core.replica right).delivered) : a = b :=
  Resdet.response_agreement (reachable_refines h) left right ha hb

theorem at_most_once_delivery (h : Reachable cfg leader s) (r : Node) :
    ((s.core.replica r).delivered.map Prod.fst).Nodup :=
  Resdet.at_most_once_delivery (reachable_refines h) r

theorem prefix_agreement (h : Reachable cfg leader s) (left right : Node) :
    (s.core.replica left).delivered <+: (s.core.replica right).delivered ∨
    (s.core.replica right).delivered <+: (s.core.replica left).delivered :=
  Resdet.prefix_agreement (reachable_refines h) left right

theorem race_winner_agreement (h : Reachable cfg leader s) (left right : Node)
    {a b : Item Request Response}
    (ha : (s.core.replica left).delivered.head? = some a)
    (hb : (s.core.replica right).delivered.head? = some b) : a.1 = b.1 :=
  Resdet.race_winner_agreement (reachable_refines h) left right ha hb

theorem applied_prefix_correct (h : Reachable cfg leader s) (r : Node) :
    (s.core.replica r).delivered = dedup (s.core.log.take (s.core.replica r).processed).flatten :=
  (Resdet.reachable_invariant (reachable_refines h)).appliedPrefixCorrect r

theorem leader_without_crashes (h : Reachable cfg leader s) (hc : cfg.crashes = false) :
    s.leader = some leader := by
  induction h with
  | init => rfl
  | step _ step ih =>
      cases step with
      | crash n enabled _ => cases enabled.symm.trans hc
      | elect n enabled _ _ => cases enabled.symm.trans hc
      | _ => exact ih

theorem senders_without_crashes (h : Reachable cfg leader s) (hc : cfg.crashes = false) :
    ∀ d ∈ s.dispatches, d.1 = leader := by
  induction h with
  | init => simp [initial]
  | step reach step ih =>
      cases step with
      | dispatch n request lead _ _ _ _ =>
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact Option.some.inj (lead.symm.trans (leader_without_crashes reach hc))
          · exact ih d hd
      | _ => exact ih

/-- One exported bundle of the normal-protocol safety obligations. Properties
which are false with fallback/failures retain their explicit mode conditions. -/
structure Safety (cfg : Config) (s : State Node Request Payload Response) : Prop where
  selection : ∀ c ∈ s.choices, Justified cfg.quorum s.ballots c
  fallback : ∀ c ∈ s.choices, c.2.2 = true → cfg.timeoutFallback = true
  selectionBeforeDispatch : ∀ d ∈ s.dispatches, Selected s d.2.1
  authorizedDispatch : ∀ d ∈ s.dispatches, d.2.2 = some d.1
  observedExecution : ∀ item ∈ s.observed, ∃ n, (n, item.1, item.2) ∈ s.executions
  executionDispatch : ∀ e ∈ s.executions, ∃ l, (e.1, e.2.1, l) ∈ s.dispatches
  proposalValidity : s.proposed ⊆ s.observed
  consensusValidity : s.core.log.flatten ⊆ s.proposed
  physicalOnce : cfg.crashes = false → (s.dispatches.map fun d => d.2.1).Nodup
  cache : CacheCoherent s
  contiguousPrefix : Resdet.Invariant s.core
  deliveryOnce : ∀ r, ((s.core.replica r).delivered.map Prod.fst).Nodup
  agreement : ∀ left right request a b,
    (request, a) ∈ (s.core.replica left).delivered →
    (request, b) ∈ (s.core.replica right).delivered → a = b
  prefixes : ∀ left right,
    (s.core.replica left).delivered <+: (s.core.replica right).delivered ∨
    (s.core.replica right).delivered <+: (s.core.replica left).delivered
  noEarlyDelivery : ∀ r item, item ∈ (s.core.replica r).delivered → item ∈ s.core.log.flatten

theorem all_safety (h : Reachable cfg leader s) : Safety cfg s :=
  { selection := selection_justified h
    fallback := fallback_explicit h
    selectionBeforeDispatch := no_dispatch_before_selection h
    authorizedDispatch := only_leader_dispatches h
    observedExecution := observed_executed h
    executionDispatch := executions_dispatched h
    proposalValidity := proposal_validity h
    consensusValidity := consensus_validity h
    physicalOnce := at_most_one_physical_dispatch h
    cache := reachable_cache h
    contiguousPrefix := Resdet.reachable_invariant (reachable_refines h)
    deliveryOnce := at_most_once_delivery h
    agreement := fun l r _ _ _ ha hb => response_agreement h l r ha hb
    prefixes := prefix_agreement h
    noEarlyDelivery := fun r _ hi => Resdet.delivered_in_log (reachable_refines h) r hi }

end Resdet.Protocol
