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

- Every record is exactly one JSON object with an `event` tag. A final line
  terminator is allowed, but an empty record in the middle is an error.
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

All three files are produced by
`tests/generate_trace_fixtures.rs::generate_all_fixtures`; they are not
handwritten protocol transcripts.

### `normal`

- Validators: nodes `01` through `07`, weight 100 each (total 700).
- Blocks: seven blocks at each of rounds 0, 1, and 2. Every round-1 block
  references every round-0 block, and likewise for round 2.
- Wave/leader: wavelength 3, wave 0 leader is node `01`'s round-0 block.
- Evidence: the real approval evaluator emits 16 unique approval facts; the
  weighted code emits seven ratification certificates and one
  super-ratification certificate.
- Expected result: the leader is finalized. Weighted `tau` emits the leader as
  its one-item output; both the exact order and running output-prefix hash are
  replayed by Lean.
- Principal trace events: 21 `insert_block`, 16 `accept_approval`, eight
  `build_threshold_certificate`, one `compute_finality`, one `run_tau_order`,
  and one `emit_output` (48 total).

### `equivocation`

- Validators: nodes `01` through `07`, weight 100 each (total 700).
- Blocks: node `07` creates two distinct incomparable round-0 blocks. Nodes
  `01` through `06` each create one round-0 block and six blocks in each of
  rounds 1 and 2; the later honest blocks acknowledge both forks.
- Wave/leader: wavelength 3, wave 0 leader is honest node `01`.
- Evidence: an actual validation call and actual equivocation scan report node
  `07`'s same-round fork; node `07` is excluded from approvals while the six
  honest validators still carry 600/700 weight. Rust emits six ratification
  certificates and one super-ratification certificate.
- Expected result: exactly the reported node-07 fork is an equivocation and
  the honest leader remains finalized. This scenario calls finality directly,
  so it intentionally has no `run_tau_order` or `emit_output` event.
- Principal trace events: 20 `insert_block`, one `validate_block`, one
  `detect_equivocation`, 13 `accept_approval`, seven certificates, and one
  `compute_finality` (43 total).

### `low_stake`

- Validators: nodes `01`–`03` have weight 1000; nodes `04`–`07` have weight 1
  (total 3004).
- Blocks: all seven validators create round-0 blocks. Only nodes
  `01,04,05,06,07` participate in rounds 1 and 2, for 17 blocks total.
- Wave/leader: wavelength 3, wave 0 leader is node `01`.
- Evidence: five validators form a count quorum, but their distinct stake is
  only 1004/3004. Rust's count-based control assertion finalizes; the weighted
  implementation does not build a certificate and returns no final leader.
- Expected result: `not_finalized`. Lean independently obtains the same answer
  from the sidecar weights and strict `3 * support > 2 * total` arithmetic.
  This direct-finality scenario intentionally has no tau/output event.
- Principal trace events: 17 `insert_block`, 57 actual approval evaluations,
  no certificate, and one `compute_finality` (75 total).

The generator executes every scenario twice and compares all six trace/config
files byte-for-byte. This catches randomized set traversal and unstable ids.

## Genuine threshold mutation

Cargo feature `trace-threshold-mutation` is a deliberately broken, test-only
feature that replaces the production predicate with `2 * support > total`.
It implies `trace` and is never used by normal builds. The mutation generator
runs the real approval → certificate → finality call path with four equally
weighted participants out of seven and writes only to a temporary directory.
`scripts/issue188_mutation_test.sh` feeds that trace to unchanged Lean code and
requires rejection. The script does not edit a recorded decision and does not
write the mutated trace into `lean/traces/`.

## Adapter and formal trust boundaries

The canonical trace deliberately omits application payload bytes and
signatures. For every accepted insertion, replay creates a formal `Block`
whose creator and predecessor set are the checked trace values. Its payload is
an injective compact insertion tag, and its id is exactly
`hashContent creator content`; therefore the original KR1 `Block.id_eq`
invariant is preserved rather than removed. `ReplayedBlock` maintains the
one-to-one association between that formal id and the externally reported Rust
digest. Duplicate Rust digests and formal-id collisions are both rejected.

Cryptographic digest/signature validation remains a Rust-side trust boundary:
Issue #188 replay checks the consensus semantics exposed by the trace, not the
signature algorithm. DAG closure, observation, equivocation, approval,
weighted certificates, finality, ordering, and output are independently
re-established in Lean.

`Ordering.lean` retains the earlier abstract `tau_prefix_monotone` axiom as a
documented KR4 prefix-safety trust boundary. Issue #188 replay does not use that
axiom as an oracle: `CMRef.computeTau` executes leader/finality/ratification/
approval selection and topological ordering over the reconstructed formal DAG,
then compares its exact result to Rust.
