# 05a — Canonical trace schema and instrumentation

Issue #188 uses newline-delimited JSON as a protocol-level interchange format:

```text
Rust execution → typed TraceEvent → NDJSON → typed Lean TraceEvent → CMRef replay
```

Tracing is compiled only with Cargo feature `trace`. Without that feature,
`trace::emit` is an inline no-op and normal consensus behavior is unchanged.
With the feature enabled, `CORDIAL_TRACE_FILE` selects an append-only file;
otherwise events go to stderr. The fixture generator truncates each target
before executing its scenario.

## Canonical encoding rules

- Every non-empty line is exactly one JSON object with an `event` tag.
- Unknown events, unknown fields, missing fields, wrong types, malformed JSON,
  and invalid enum strings are errors in Lean.
- Required nullable fields are present as JSON `null`; omission is not treated
  as null. Lean represents them as `Option`.
- Block, parent, approver, and output arrays preserve all schema data. Set-valued
  Rust inputs are sorted before emission.
- `scheduler_tick.tick` is a deterministic logical step, never wall-clock time.
- Weight-table, certificate, and output-prefix fingerprints use FNV-1a-64 with
  the encodings documented in `crates/cordial-miners-core/src/trace.rs`.

## Complete event catalogue

| Event | Required payload fields | Runtime emission site |
|---|---|---|
| `create_block` | `node_id`, `wave?`, `round?`, `block_hash`, `parent_hashes`, `missing_parent_hashes`, `creator`, `weight_table_hash?` | `network::Node::create_block` before insertion |
| `validate_block` | lifecycle identity fields, `outcome`, `errors` | `consensus::validation::validate_block` |
| `insert_block` | all lifecycle fields | `Blocklace::commit_validated`, shared by both insertion APIs |
| `buffer_block` | all lifecycle fields, complete `missing_parent_hashes` | closure failure and `SimNode::receive_block` |
| `resolve_missing_parent` | `node_id`, `block_hash`, `resolved_parent_hash` | `SimNode::retry_buffered_blocks` |
| `detect_equivocation` | `node_id`, `equivocator`, `round`, `conflicting_block_hashes` | `consensus::cordiality::all_equivocations` |
| `accept_approval` | `node_id`, `wave?`, `round`, `approver`, `approver_hash`, `target_hash` | memoized approval evaluation |
| `build_threshold_certificate` | `node_id`, `wave?`, `kind`, `leader_hash`, `ratifier_hash?`, `certificate_id`, `approver_hashes`, `approvers`, `approver_count`, `approver_weight`, `total_weight`, `weight_table_hash` | weighted ratification and super-ratification |
| `compute_finality` | `node_id`, `wave`, `wavelength`, `block_hash`, `decision`, `certificate_id?`, `output_prefix_hash?`, `weight_table_hash` | weighted and unweighted final-leader evaluation |
| `run_tau_order` | `node_id`, `wave`, `wavelength`, `latest_leader_hash`, `ordered_block_hashes`, `output_len` | weighted and unweighted `tau` |
| `emit_output` | `node_id`, `wave`, `block_hash`, `output_index`, `output_prefix_hash` | each `tau` output item |
| `send_package` | `node_id`, `peer_id`, `block_hashes` | network node and adversarial simulator send paths |
| `deliver_package` | `node_id`, `peer_id`, `block_hashes` | network node and adversarial simulator delivery paths |
| `scheduler_tick` | `node_id`, `tick`, `wave?` | deterministic adversarial scheduler advance |
| `run_wave_task` | `node_id`, `wave`, `task` | simulated finality wave task (`finalize`) |

The Rust round-trip unit test and `lean/traces/schema_all_events.json` cover all
15 variants. The latter is synthetic parser data only. Consensus fixtures are
generated exclusively by real consensus calls. The runtime instrumentation
test separately drives out-of-order dissemination and scheduling to prove the
transport/buffer/task variants are emitted at real call sites.

## Blocklace and nullable values

`round` is `null` when a missing predecessor prevents DAG depth calculation;
it is never replaced with zero. `BufferBlock` records every currently missing
parent. Each later `ResolveMissingParent` removes exactly one member, and an
`InsertBlock` is accepted only after the set is empty. Replay rejects dangling,
duplicate, or unknown predecessors and preserves a proof of `ValidBlocklace`
after every insertion.

## Weight configuration

Each scenario has a sidecar `NAME.weights.json` containing:

- the sorted validator id/weight table;
- a strictly sorted, unique wave-to-leader table;
- the positive wavelength; and
- the expected FNV-1a-64 table hash.

Lean parses the table, recomputes its hash, checks every referenced validator
and leader, and uses the weights for `3 * support > 2 * total`. A hash alone is
never treated as quorum evidence.

## Canonical scenarios

| Scenario | Actual properties exercised |
|---|---|
| `normal` | 21 insertions, approvals, ratification/super-ratification certificates, finalized leader, τ, output item and prefix hash |
| `equivocation` | valid insertion/validation, node 7 same-round fork detection, approvals/certificates, and safe finality of honest leader node 1 |
| `low_stake` | five voters by count but only 1004/3004 stake; count finality succeeds in the Rust scenario assertion while weighted Rust and Lean finality reject |

The generator executes every scenario twice and compares all six trace/config
files byte-for-byte. This catches randomized set traversal and unstable ids.

## Adapter and formal trust boundaries

The trace does not expose payload or signatures. Replay interns each unique
Rust block hash as a fresh opaque formal `BlockId`, retains creator and parent
edges, and dynamically rejects duplicate hashes. Cryptographic validation of
the digest/signature remains on the Rust side; DAG closure and all consensus
predicates are re-established in Lean.

`Ordering.lean` retains the earlier abstract `tau_prefix_monotone` axiom as a
documented KR4 prefix-safety trust boundary. Issue #188 replay does not use that
axiom as an oracle: `CMRef.computeTau` executes leader/finality/ratification/
approval selection and topological ordering over the reconstructed formal DAG,
then compares its exact result to Rust.
