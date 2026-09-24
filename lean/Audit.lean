import Resdet
import Tests
import Lean

/-!
Reject extra axioms transitively, including unfinished proofs and native
evaluation axioms. Protocol assumptions are in the model, not added axioms.
Only Lean's standard logical foundations are allowed here.
-/
open Lean Elab Command in
run_cmd do
  let required := #[`Resdet.reachable_invariant, `Resdet.response_agreement,
    `Resdet.at_most_once_delivery, `Resdet.delivery_count_le_one,
    `Resdet.prefix_agreement, `Resdet.race_winner_agreement,
    `Resdet.delivered_in_log, `Resdet.step_delivery_monotone,
    `Resdet.Tests.sample_reachable, `Resdet.Tests.skipped_prefix_unreachable,
    `Resdet.Tests.early_delivery_unreachable,
    `Resdet.Protocol.reachable_cache, `Resdet.Protocol.reachable_refines,
    `Resdet.Protocol.selection_justified, `Resdet.Protocol.only_leader_dispatches,
    `Resdet.Protocol.response_validity, `Resdet.Protocol.at_most_one_physical_dispatch,
    `Resdet.Protocol.response_agreement, `Resdet.Protocol.prefix_agreement,
    `Resdet.Protocol.all_safety, `Resdet.Protocol.eventual_exactly_once,
    `Resdet.Protocol.eventual_delivery_stable_consensus,
    `Resdet.Protocol.exactly_once_stable_consensus,
    `Resdet.Protocol.eventual_delivery, `Resdet.eventually_processed,
    `Resdet.agreed_eventually_delivered, `Resdet.Protocol.Tests.recovery_run,
    `Resdet.Protocol.Tests.fairness_is_necessary,
    `Resdet.Protocol.Tests.progress_contracts_satisfiable,
    `Resdet.Protocol.Tests.retry_contracts_satisfiable,
    `Resdet.Protocol.Tests.reproposal_reachable,
    `Resdet.Paper.lemma_1_same_processed_entry,
    `Resdet.Paper.lemma_2_no_hole_processing,
    `Resdet.Paper.theorem_1_safety, `Resdet.Paper.theorem_2_liveness,
    `Resdet.Paper.first_committed_response,
    `Resdet.Paper.eventually_prefix_learned,
    `Resdet.Paper.batching_equivalent, `Resdet.Paper.rebatching_preserves_delivery,
    `Resdet.Paper.race_winner_for_group, `Resdet.Paper.deterministic_continuation,
    `Resdet.Paper.Tests.batch_boundaries_do_not_change_result,
    `Resdet.Paper.Tests.recovery_marker_counterexample,
    `Resdet.Paper.Tests.paper_contracts_satisfiable,
    `Resdet.Paper.eventually_agreed, `Resdet.Paper.eventually_delivered,
    `Resdet.Paper.single_arrival_ready, `Resdet.Paper.fallback_arrival_ready,
    `Resdet.Paper.theorem_1_crash_stop, `Resdet.Paper.theorem_2_crash_stop,
    `Resdet.Paper.CrashStopBehavior.permanently_down,
    `Resdet.Paper.CrashStopBehavior.stable_leader_nonfaulty,
    `Resdet.Paper.CrashStopTests.failover_retry_run,
    `Resdet.Paper.CrashStopTests.failed_node_cannot_rejoin,
    `Resdet.Paper.CrashStopTests.crash_stop_contracts_satisfiable]
  for name in required do
    let _ ← getConstInfo name
  let allowed := #[`propext, `Quot.sound, `Classical.choice]
  let mut checked := 0
  for (name, _) in (← getEnv).constants.toList do
    if `Resdet |>.isPrefixOf name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
      checked := checked + 1
  if checked == 0 then throwError "No Resdet declarations were audited"
  logInfo m!"Axiom audit passed for {checked} Resdet declarations (including tests)."

#print axioms Resdet.reachable_invariant
#print axioms Resdet.response_agreement
#print axioms Resdet.at_most_once_delivery
#print axioms Resdet.prefix_agreement
#print axioms Resdet.race_winner_agreement
#print axioms Resdet.Protocol.reachable_refines
#print axioms Resdet.Protocol.response_validity
#print axioms Resdet.Protocol.eventual_delivery
#print axioms Resdet.Protocol.eventual_delivery_stable_consensus
#print axioms Resdet.Paper.theorem_1_safety
#print axioms Resdet.Paper.theorem_2_liveness
#print axioms Resdet.Paper.batching_equivalent
#print axioms Resdet.Paper.theorem_2_crash_stop
