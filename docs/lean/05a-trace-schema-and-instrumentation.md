# 05a — Trace Schema and Instrumentation

**Target branch:** `lean-q1-kr5-trace-replay`
**Owned by:** Issue 188 (KR5 — Proof-to-Test Mapping and Trace Replay)

---

## Overview

`cordial-miners-core` can emit a newline-delimited JSON trace of every
safety-relevant consensus decision it makes. This document defines:

1. The full event catalogue (types, fields, semantics).
2. How to enable tracing.
3. Where the canonical fixture corpus lives.
4. Schema stability guarantees.

---

## Enabling Tracing

Tracing is behind a Cargo feature flag so it compiles away to zero overhead
in normal builds:

```toml
# Cargo.toml
[features]
trace = []   # already present; no new deps
```

Enable during tests:

```bash
# Write to a file
CORDIAL_TRACE_FILE=lean/traces/normal.json \
  cargo test --features trace --test generate_trace_fixtures generate_all_fixtures \
  -- --nocapture

# Or write to stderr (no env var needed)
cargo test --features trace ...
```

The `CORDIAL_TRACE_FILE` environment variable specifies the output path.
If unset, events are written to `stderr`. The file is opened in append mode,
so multiple test runs accumulate in the same file; delete it before each run
to start fresh.

---

## Event Catalogue

All events are serialized as **newline-delimited JSON** (one JSON object per
line). Every object has an `event` field carrying the event kind; all other
fields are event-specific.

### Block Lifecycle

#### `insert_block`
Emitted when a block is successfully inserted into the local blocklace.

```json
{
  "event": "insert_block",
  "node_id":          "01",
  "wave":             null,
  "round":            0,
  "block_hash":       "0101000000000000000000000000000000000000000000000000000000000000",
  "parent_hashes":    [],
  "creator":          "01",
  "weight_table_hash": null
}
```

| Field | Type | Description |
|---|---|---|
| `node_id` | hex string | Hex-encoded creator public key (= `NodeId` bytes) |
| `wave` | `u64` or `null` | Wave index; `null` if wavelength not configured |
| `round` | `u64` | DAG depth of the block |
| `block_hash` | hex string | Blake2b-256 content hash of the block |
| `parent_hashes` | `[hex string]` | Content hashes of direct predecessor blocks |
| `creator` | hex string | Same as `node_id` (kept for Lean-side symmetry) |
| `weight_table_hash` | hex string or `null` | Blake2b-256 of the current bond table |

#### `validate_block`
Emitted at the end of `validate_block()`, carrying the validation outcome.

```json
{
  "event": "validate_block",
  "node_id": "01",
  "wave": 0,
  "round": 0,
  "block_hash": "0101...",
  "parent_hashes": [],
  "creator": "01",
  "weight_table_hash": null,
  "outcome": "valid",
  "errors": []
}
```

Additional fields:

| Field | Type | Values |
|---|---|---|
| `outcome` | string | `"valid"` \| `"invalid"` |
| `errors` | `[string]` | Human-readable list of validation errors (empty on success) |

#### `buffer_block`
Emitted when a block fails the closure axiom check (a predecessor is not yet
in the local blocklace). The block is not inserted — it should be buffered by
the caller until the missing parent arrives.

Fields: same as `insert_block`.

#### `resolve_missing_parent`
Emitted when a previously-buffered block is released after its missing
predecessor arrives.

```json
{
  "event": "resolve_missing_parent",
  "node_id":              "01",
  "block_hash":           "0101...",
  "resolved_parent_hash": "0202..."
}
```

---

### Equivocation

#### `detect_equivocation`
Emitted inside `all_equivocations()` whenever a same-round equivocation is
found in the blocklace.

```json
{
  "event": "detect_equivocation",
  "node_id":    "01",
  "equivocator": "01",
  "round":       0,
  "conflicting_block_hashes": [
    "0101000000000000000000000000000000000000000000000000000000000000",
    "0102000000000000000000000000000000000000000000000000000000000000"
  ]
}
```

| Field | Type | Description |
|---|---|---|
| `node_id` | hex string | Observer node (proxy: equivocator id at this call site) |
| `equivocator` | hex string | The validator that equivocated |
| `round` | `u64` | Round at which the equivocation occurred |
| `conflicting_block_hashes` | `[hex string]` | All incomparable blocks by the equivocator at this round |

---

### Approval and Certificates

#### `accept_approval`
Emitted when a block approves another (per Definition 18 of the CM paper).

```json
{
  "event": "accept_approval",
  "node_id":       "02",
  "wave":          0,
  "approver_hash": "0210...",
  "target_hash":   "0101..."
}
```

#### `build_threshold_certificate`
Emitted when a super-majority approval certificate is assembled for a leader
block.

```json
{
  "event": "build_threshold_certificate",
  "node_id":        "01",
  "wave":           1,
  "leader_hash":    "0101...",
  "certificate_id": "cert_01",
  "approver_count": 5,
  "approver_weight": 500
}
```

| Field | Type | Description |
|---|---|---|
| `approver_count` | `u64` | Number of distinct approving validators |
| `approver_weight` | `u64` or `null` | Summed bonded stake; `null` in unweighted mode |

---

### Finality

#### `compute_finality`
Emitted by `is_final_leader()` for every leader block evaluated.

```json
{
  "event": "compute_finality",
  "node_id":           "01",
  "wave":              0,
  "block_hash":        "0101...",
  "decision":          "finalized",
  "certificate_id":    null,
  "output_prefix_hash": null
}
```

| Field | Type | Values |
|---|---|---|
| `decision` | string | `"finalized"` \| `"not_finalized"` |
| `certificate_id` | string or `null` | Certificate id if finalized; absent otherwise |
| `output_prefix_hash` | hex string or `null` | Running output-prefix hash at finalization |

---

### Ordering

#### `run_tau_order`
Emitted once per `tau()` invocation, summarizing the ordering result.

```json
{
  "event": "run_tau_order",
  "node_id":            "01",
  "wave":               1,
  "latest_leader_hash": "0220...",
  "output_len":         22
}
```

#### `emit_output`
Emitted for each block appended to the canonical output prefix, with a running
prefix hash for end-to-end consistency checking.

```json
{
  "event": "emit_output",
  "node_id":           "01",
  "wave":              1,
  "block_hash":        "0201...",
  "output_index":      0,
  "output_prefix_hash": "a3b4..."
}
```

---

### Dissemination

#### `send_package` / `deliver_package`
Emitted when a batch of blocks is sent to or received from a peer.

```json
{
  "event": "send_package",
  "node_id":     "01",
  "peer_id":     "02",
  "block_hashes": ["0101...", "0202..."]
}
```

---

### Scheduler

#### `scheduler_tick`
Emitted when the consensus scheduler timer fires.

```json
{
  "event": "scheduler_tick",
  "node_id":      "01",
  "timestamp_ms": 1700000000000,
  "wave":         1
}
```

#### `run_wave_task`
Emitted when a wave-level task is dispatched.

```json
{
  "event": "run_wave_task",
  "node_id": "01",
  "wave":    1,
  "task":    "propose"
}
```

Valid `task` values: `"propose"` | `"vote"` | `"finalize"`.

---

## Instrumented Call Sites

| Event | Source file | Function |
|---|---|---|
| `insert_block` | `src/blocklace.rs` | `Blocklace::insert()` |
| `buffer_block` | `src/blocklace.rs` | `Blocklace::insert()` (closure failure path) |
| `validate_block` | `src/consensus/validation.rs` | `validate_block()` |
| `detect_equivocation` | `src/consensus/cordiality.rs` | `all_equivocations()` |
| `compute_finality` | `src/consensus/finality.rs` | `is_final_leader()` |
| `run_tau_order` | `src/consensus/ordering.rs` | `tau()` |
| `emit_output` | `src/consensus/ordering.rs` | `tau()` (per-block loop) |

> **Note:** `accept_approval`, `build_threshold_certificate`, `send_package`,
> `deliver_package`, `scheduler_tick`, and `run_wave_task` are defined in the
> schema and round-trip through JSON correctly, but call-site instrumentation
> for these is deferred until the dissemination and scheduler modules are
> implemented (Issue 06+). The Lean parser handles all variants today.

---

## Fixture Corpus

Three canonical trace files are committed under `lean/traces/`:

| File | Scenario | Key events |
|---|---|---|
| `normal.json` | 7-node happy-path, 2 waves (n=7, f=2, wavelength=3) | `insert_block` × 42, `compute_finality` × 14, `run_tau_order` × 1, `emit_output` × 22 |
| `equivocation.json` | Node 1 equivocates at round 0, 7 nodes | `insert_block` × 13, `detect_equivocation` × 1 |
| `low_stake.json` | 7 nodes, node 7 has stake=1; weighted finality | `insert_block` × 42, `compute_finality` × 14 |

Generate fresh fixtures with:

```bash
rm -f lean/traces/*.json
cargo test --features trace --test generate_trace_fixtures generate_all_fixtures -- --nocapture
```

---

## Schema Stability Contract

Every field name and type in `src/trace.rs::TraceEvent` has a direct
corresponding field in `lean/LeanVerification/Trace.lean`. Any change to
either must be accompanied by a matching change in the other. The
`all_variants_serialize_with_event_tag` unit test in `src/trace.rs` enforces
round-trip JSON correctness for every variant on every `cargo test` run.
