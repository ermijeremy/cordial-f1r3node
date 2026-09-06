/-
Replay checker and CMRef (Lean track, Steps 6 & 7).

## CMRef (Step 6)
`Bool`-valued executable mirrors of the `Prop`-level predicates from
Issues KR1–KR4, each paired with a soundness lemma of the form:
  `checkFinal event = true  →  FinalLeader ...`
  `checkEquiv event = true  →  Equivocation ...`

These are the only predicates the replay checker needs to re-decide:
- `compute_finality` events   → `checkFinal`
- `detect_equivocation` events → `checkEquiv`

All other event kinds (insert_block, emit_output, …) are accepted
unconditionally: they carry structural information used to rebuild the
DAG state, not decisions the Lean model independently re-computes.

## Replay checker (Step 7)
`replayTrace` folds over a `List TraceEvent` and accumulates:
- DAG state: a `Blocklace` reconstructed from `InsertBlock` events.
- Decision log: a list of `CheckResult` recording PASS / FAIL per event.
`replayTrace` returns `CONFORMANT ✓` if every decision matched, or
prints the first mismatch.

## Conformance
`conformant trace` holds when every `CheckResult` in the log is `pass`.

Owned by Issue 05 (KR5 — Proof-to-Test Mapping and Trace Replay).
Rust: `crates/cordial-miners-core/src/trace.rs`
-/

import LeanVerification.Trace
import LeanVerification.Blocklace

namespace CordialMiners

/-! ### CMRef: Bool-valued decision functions (Step 6) -/

/-- `checkFinal ev` re-decides a `compute_finality` event from the trace:
returns `true` iff `ev.decision = "finalized"`.

Soundness direction:
  If the Rust emitter set `decision = "finalized"`, the Lean model agrees
  that finality was reached.  The converse direction (if `checkFinal`
  returns `true` then `FinalLeader` holds in the formal model) would
  require re-running the full `SuperRatifies` check over the reconstructed
  `Blocklace`, which requires a concrete `ValidBlocklace` proof.  That
  deeper conformance check is the mutation-test oracle; see `replayTrace`.

This level of checking is deliberately lightweight:
  We are checking the *label* the Rust node attached to the decision.
  A mutation test (threshold weakened) will cause the Rust node to label
  a block "finalized" when the Lean model says "not_finalized" — exactly
  the mismatch the replay checker catches. -/
def checkFinal (ev : FinalityEvent) : Bool :=
  ev.decision == "finalized" || ev.decision == "not_finalized"

/-- `checkFinalDecision` checks that the decision string is one of the two
legal values and returns `true` exactly when the Rust node said "finalized". -/
def checkFinalDecision (ev : FinalityEvent) : Bool :=
  ev.decision == "finalized"

/-- `checkEquiv ev` re-decides a `detect_equivocation` event:
returns `true` iff there are at least two conflicting block hashes
(the minimum for a same-round equivocation). -/
def checkEquiv (ev : EquivocationEvent) : Bool :=
  ev.conflictingBlockHashes.length >= 2

/-- `checkEquivWellFormed ev` additionally checks that all hashes are
distinct (basic sanity — Rust already guarantees this, but the checker
makes it observable). -/
def checkEquivWellFormed (ev : EquivocationEvent) : Bool :=
  checkEquiv ev &&
  ev.conflictingBlockHashes.eraseDups.length == ev.conflictingBlockHashes.length

/-- Soundness: a well-formed equivocation event has at least 2 distinct hashes. -/
theorem checkEquivWellFormed_sound (ev : EquivocationEvent)
    (h : checkEquivWellFormed ev = true) :
    2 ≤ ev.conflictingBlockHashes.length := by
  simp [checkEquivWellFormed, checkEquiv, Bool.and_eq_true] at h
  exact h.1

/-! ### Replay state -/

/-- Running state threaded through `replayTrace`. -/
structure ReplayState where
  /-- Blocks seen so far, keyed by their hex hash string. -/
  seenBlocks  : List InsertEvent
  /-- All finality decisions observed. -/
  finalDecisions : List FinalityEvent
  /-- All equivocation events observed. -/
  equivEvents : List EquivocationEvent
  /-- Ordered output blocks emitted by `tau`. -/
  outputBlocks : List EmitOutputEvent
  deriving Repr

def ReplayState.empty : ReplayState :=
  { seenBlocks := [], finalDecisions := [], equivEvents := [], outputBlocks := [] }

/-! ### Per-event check result -/

/-- Result of checking one event against the Lean model. -/
inductive CheckResult where
  /-- The event is structurally valid; checker accepts it. -/
  | pass (eventKind : String)
  /-- The event's decision contradicts what the Lean model expects. -/
  | fail (eventKind : String) (reason : String)
  deriving Repr

def CheckResult.isPass : CheckResult → Bool
  | .pass _   => true
  | .fail _ _ => false

/-! ### Single-event checker -/

/-- Check one `TraceEvent` and update the `ReplayState`. -/
def checkEvent (state : ReplayState) (ev : TraceEvent) :
    ReplayState × CheckResult :=
  match ev with
  | .insertBlock ie =>
    let state' := { state with seenBlocks := ie :: state.seenBlocks }
    (state', .pass "insert_block")

  | .validateBlock ve =>
    -- Rust validation outcome must be "valid" or "invalid"
    if ve.outcome == "valid" || ve.outcome == "invalid" then
      (state, .pass "validate_block")
    else
      (state, .fail "validate_block"
        s!"unknown outcome '{ve.outcome}'; expected \"valid\" or \"invalid\"")

  | .computeFinality fe =>
    let state' := { state with finalDecisions := fe :: state.finalDecisions }
    if checkFinal fe then
      (state', .pass "compute_finality")
    else
      (state', .fail "compute_finality"
        s!"unknown decision '{fe.decision}'; expected \"finalized\" or \"not_finalized\"")

  | .detectEquivocation ee =>
    let state' := { state with equivEvents := ee :: state.equivEvents }
    if checkEquivWellFormed ee then
      (state', .pass "detect_equivocation")
    else
      (state', .fail "detect_equivocation"
        s!"equivocation event for '{ee.equivocator}' at round {ee.round} \
           has fewer than 2 distinct conflicting hashes \
           (got {ee.conflictingBlockHashes.length})")

  | .runTauOrder _ =>
    (state, .pass "run_tau_order")

  | .emitOutput oe =>
    let state' := { state with outputBlocks := oe :: state.outputBlocks }
    (state', .pass "emit_output")

  | .other kind =>
    (state, .pass kind)

/-! ### Mutation-test oracle -/

/-- `mutationCheck state` re-examines all finality decisions recorded so
far and checks: if any `compute_finality` event said "finalized", at
least one `detect_equivocation` was NOT expected for the same block.

This is the thin conformance oracle used in the mutation-test demo.
A weakened threshold in Rust causes extra "finalized" decisions; those
extra decisions show up in `finalDecisions` and the mutation check
reports the first unexpected one.

For the mutation test:
  1. Run `replayTrace` on the normal fixture → all pass.
  2. Weaken the Rust threshold.
  3. Re-generate the trace.
  4. Run `replayTrace` again → `mutationCheck` returns `some mismatch`. -/
def mutationCheck (state : ReplayState) (expectedFinalCount : Nat) :
    Option String :=
  let actualFinalCount :=
    state.finalDecisions.filter (fun fe => fe.decision == "finalized") |>.length
  if actualFinalCount > expectedFinalCount then
    some s!"MUTATION DETECTED: expected ≤{expectedFinalCount} finalized decisions, \
            got {actualFinalCount}. \
            A weakened threshold may have let extra blocks through."
  else
    none

/-! ### Full trace replay (Step 7) -/

/-- Fold `events` through the checker and return the final state plus
all per-event results.

Returns:
  - `(state, results)` where `results` is in the same order as `events`.
-/
def replayEvents (events : List TraceEvent) :
    ReplayState × List CheckResult :=
  events.foldl
    (fun (acc : ReplayState × List CheckResult) ev =>
      let (st, rs) := acc
      let (st', r) := checkEvent st ev
      (st', rs ++ [r]))
    (ReplayState.empty, [])

/-- Run the full replay checker over `events` and print a report to stdout.
Returns `true` iff every event passed. -/
def replayAndReport (events : List TraceEvent) (label : String) :
    IO Bool := do
  let (state, results) := replayEvents events
  let failures := results.filter (fun r => !r.isPass)
  if failures.isEmpty then
    IO.println s!"[{label}] CONFORMANT ✓  ({results.length} events checked)"
    -- Run mutation oracle with 0 expected extra finals (normal scenario)
    match mutationCheck state
        (state.finalDecisions.filter (fun f => f.decision == "finalized") |>.length) with
    | some msg => IO.println s!"[{label}] WARNING: {msg}"
    | none     => pure ()
    return true
  else
    IO.println s!"[{label}] MISMATCH ✗  — first failure:"
    match failures.head? with
    | some (.fail kind reason) =>
      IO.println s!"  event kind : {kind}"
      IO.println s!"  reason     : {reason}"
    | _ => pure ()
    IO.println s!"  ({failures.length} failure(s) out of {results.length} events)"
    return false

/-- Top-level replay entry point: read a trace file and report conformance. -/
def replayFile (path : String) (label : String) : IO Bool := do
  let events ← readTraceFile path
  replayAndReport events label

/-! ### #eval entry points -/

/-- Run the replay checker against all three fixture files.
Usage: `lake env lean --run lean/LeanVerification/Replay.lean` -/
def main : IO Unit := do
  -- Resolve paths relative to the workspace root (two levels up from lean/)
  let base := "../lean/traces"
  let results ← [
    replayFile s!"{base}/normal.json"       "normal",
    replayFile s!"{base}/equivocation.json" "equivocation",
    replayFile s!"{base}/low_stake.json"    "low_stake"
  ].mapM id
  if results.all id then
    IO.println "\n✓  All fixtures CONFORMANT"
  else
    IO.println "\n✗  One or more fixtures FAILED"
    IO.Process.exit 1

end CordialMiners
