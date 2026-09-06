-- replay_runner.lean
-- Run: lake env lean --run lean/replay_runner.lean

import LeanVerification.Replay

open CordialMiners

def main (args : List String) : IO Unit := do
  let base := "traces"
  let scenarios := if args.isEmpty then ["normal", "equivocation", "low_stake"] else args
  let results ← scenarios.mapM fun label => do
    IO.println s!"[{label}] replaying..."
    replayFile s!"{base}/{label}.json" s!"{base}/{label}.weights.json" label
  if results.all id then
    IO.println "\n✓  All fixtures CONFORMANT"
  else
    IO.println "\n✗  One or more fixtures FAILED"
    IO.Process.exit 1
