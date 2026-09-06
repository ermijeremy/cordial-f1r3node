# 05c — Conformance CI and triage

## Reproducible pipeline

Run the full local pipeline with:

```bash
just issue188-conformance
```

Its substantive commands are:

```bash
cargo build -j 2 -p cordial-miners-core
cargo test -j 2 -p cordial-miners-core
cargo test -j 2 -p cordial-miners-core --features trace
cargo test -j 2 -p cordial-miners-core --features trace \
  --test generate_trace_fixtures generate_all_fixtures -- \
  --exact --nocapture --test-threads=1
cd lean
lake build replay_runner conformance_tests
lake exe replay_runner
lake exe conformance_tests
```

The Lake targets pass `-j 2` to Lean through `moreLeanArgs`. Cargo commands use
two jobs, and fixture generation is explicitly single-threaded because it
changes the process-local trace sink. CI runs Rust default mode before trace
mode, regenerates and diffs committed fixtures, builds Lean, replays positive
fixtures, rejects negative/mutation cases, and scans the Lean build for
`declaration uses 'sorry'`.

## Expected results

```text
[normal] CONFORMANT ✓
[equivocation] CONFORMANT ✓
[low_stake] CONFORMANT ✓

[negative/invalid-finality] rejected ✓
...
[negative/weakened-threshold-mutation] rejected ✓
```

The fixture generator also reports deterministic byte-for-byte regeneration.
A schema change that is not reflected in Lean, a changed canonical trace, a
formal mismatch, an accepted mutation, or a `sorry` makes CI fail.

## First-mismatch diagnostics

Parsing errors include a one-based line number. Replay errors include a
one-based event number. Finality failures additionally show node, wave, block,
the Rust decision, the Lean CMRef decision, support/total weight, and the
strict-threshold formula. Certificate, equivocation, τ and output failures name
the relevant hashes and the independently computed value.

Triage the first mismatch by layer:

| Diagnostic | First place to inspect |
|---|---|
| `line N` JSON/schema error | Rust `trace.rs` and Lean `Trace.lean` |
| missing/duplicate predecessor or wrong round | instrumentation order and replayed Blocklace |
| weight-table hash mismatch | sidecar ordering/weights and FNV encoding |
| approval/equivocation predicate rejects | Rust KR2 behavior vs `CMRef`/formal KR2 model |
| certificate or finality mismatch | approval evidence, stake arithmetic, leader/wave configuration |
| τ/order mismatch | latest finalized leader, recursive ratification, hash tie-break order |
| output prefix mismatch | output index/order or FNV prefix encoding |

Do not resolve a mismatch by accepting both decisions or skipping malformed
events. Determine whether it is a Rust behavior bug, a trace/schema adapter
bug, or a Lean formal-model bug, then keep the independent comparison intact.

## Mutation record

The permanent threshold mutation test changes the low-stake trace's Rust claim
from `not_finalized` to `finalized` (the behavior produced by an incorrect
count/half threshold) and supplies a fake certificate id. CMRef still computes
1004 of 3004 stake and rejects the decision as a finality mismatch. Restoring
the genuine weighted Rust result makes the positive low-stake replay pass.
