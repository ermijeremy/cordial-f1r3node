//! Trace emitter for Cordial Miners consensus decisions.
//!
//! When compiled without the `trace` feature this module compiles away to nothing.
//! When enabled, each event is serialized as a newline-delimited JSON record and
//! appended to `CORDIAL_TRACE_FILE`, or written to stderr if that variable is unset.
//!
//! Schema changes here must be mirrored in `lean/LeanVerification/Trace.lean`.

use serde::{Deserialize, Serialize};

// Event catalogue

/// A safety-relevant consensus event.
///
/// Serialized with `#[serde(tag = "event")]` so every JSON object carries an
/// `"event"` discriminant field. `Option` fields are omitted when absent.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "event", rename_all = "snake_case")]
pub enum TraceEvent {
    // Block lifecycle
    CreateBlock(BlockLifecycleEvent),
    ValidateBlock(ValidateBlockEvent),
    InsertBlock(BlockLifecycleEvent),
    /// Emitted when a predecessor is missing; block is not inserted.
    BufferBlock(BlockLifecycleEvent),
    ResolveMissingParent(ResolveMissingParentEvent),

    // Equivocation
    DetectEquivocation(DetectEquivocationEvent),

    // Approval and threshold certificates
    AcceptApproval(AcceptApprovalEvent),
    BuildThresholdCertificate(ThresholdCertificateEvent),

    // Finality
    ComputeFinality(ComputeFinalityEvent),

    // Ordering
    RunTauOrder(TauOrderEvent),
    EmitOutput(EmitOutputEvent),

    // Dissemination
    SendPackage(PackageEvent),
    DeliverPackage(PackageEvent),

    // Scheduler
    SchedulerTick(SchedulerTickEvent),
    RunWaveTask(WaveTaskEvent),
}

// Per-event payload structs

/// Shared fields for block-lifecycle events (Create / Insert / Buffer).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockLifecycleEvent {
    pub node_id: String,
    pub wave: Option<u64>,
    pub round: u64,
    pub block_hash: String,
    pub parent_hashes: Vec<String>,
    /// Block author (= NodeId bytes, hex-encoded).
    pub creator: String,
    /// Blake2b-256 of the bond table; `None` in unweighted mode.
    pub weight_table_hash: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidateBlockEvent {
    pub node_id: String,
    pub wave: Option<u64>,
    pub round: u64,
    pub block_hash: String,
    pub parent_hashes: Vec<String>,
    pub creator: String,
    pub weight_table_hash: Option<String>,
    /// `"valid"` | `"invalid"`
    pub outcome: String,
    pub errors: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResolveMissingParentEvent {
    pub node_id: String,
    pub block_hash: String,
    pub resolved_parent_hash: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectEquivocationEvent {
    /// Observer node.
    pub node_id: String,
    /// The validator that produced two incomparable blocks at the same round.
    pub equivocator: String,
    pub round: u64,
    pub conflicting_block_hashes: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AcceptApprovalEvent {
    pub node_id: String,
    pub wave: Option<u64>,
    pub approver_hash: String,
    pub target_hash: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ThresholdCertificateEvent {
    pub node_id: String,
    pub wave: u64,
    pub leader_hash: String,
    pub certificate_id: String,
    pub approver_count: usize,
    /// `None` in unweighted mode.
    pub approver_weight: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComputeFinalityEvent {
    pub node_id: String,
    pub wave: u64,
    pub block_hash: String,
    /// `"finalized"` | `"not_finalized"`
    pub decision: String,
    pub certificate_id: Option<String>,
    pub output_prefix_hash: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TauOrderEvent {
    pub node_id: String,
    pub wave: u64,
    pub latest_leader_hash: String,
    pub output_len: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmitOutputEvent {
    pub node_id: String,
    pub wave: u64,
    pub block_hash: String,
    pub output_index: usize,
    /// Running Blake2b-256 hash of the output prefix after this block.
    pub output_prefix_hash: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageEvent {
    pub node_id: String,
    pub peer_id: String,
    pub block_hashes: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchedulerTickEvent {
    pub node_id: String,
    pub timestamp_ms: u64,
    pub wave: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WaveTaskEvent {
    pub node_id: String,
    pub wave: u64,
    /// `"propose"` | `"vote"` | `"finalize"`
    pub task: String,
}

// Emission helpers: the public API used by consensus modules

/// Serialize `event` to JSON and append it to `CORDIAL_TRACE_FILE` (or stderr).
/// Write errors are silently ignored so a broken sink never aborts the node.
#[cfg(feature = "trace")]
pub fn emit(event: TraceEvent) {
    use std::fs::OpenOptions;
    use std::io::Write;

    let line = match serde_json::to_string(&event) {
        Ok(s) => s,
        Err(_) => return,
    };

    if let Ok(path) = std::env::var("CORDIAL_TRACE_FILE") {
        if let Ok(mut file) = OpenOptions::new().create(true).append(true).open(&path) {
            let _ = writeln!(file, "{}", line);
        }
    } else {
        eprintln!("[TRACE] {}", line);
    }
}

/// No-op stub compiled when the `trace` feature is disabled.
#[cfg(not(feature = "trace"))]
#[inline(always)]
pub fn emit(_event: TraceEvent) {}

// Helpers

/// Hex-encode a byte slice into a lowercase hex string.
pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

/// Blake2b-256 fingerprint of a bond table (sorted for determinism).
pub fn weight_table_hash(bonds: &std::collections::HashMap<crate::types::NodeId, u64>) -> String {
    use blake2::{Blake2b, Digest, digest::consts::U32};

    let mut entries: Vec<_> = bonds.iter().collect();
    entries.sort_by_key(|(node, _)| node.0.as_slice());

    let mut h = Blake2b::<U32>::new();
    for (node, weight) in entries {
        h.update(&(node.0.len() as u64).to_le_bytes());
        h.update(&node.0);
        h.update(&weight.to_le_bytes());
    }
    hex(&h.finalize())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every variant must round-trip through JSON with the `"event"` tag intact.
    #[test]
    fn all_variants_serialize_with_event_tag() {
        let events: Vec<TraceEvent> = vec![
            TraceEvent::CreateBlock(BlockLifecycleEvent {
                node_id: "v1".into(), wave: Some(0), round: 0,
                block_hash: "aabb".into(), parent_hashes: vec![],
                creator: "deadbeef".into(), weight_table_hash: None,
            }),
            TraceEvent::ValidateBlock(ValidateBlockEvent {
                node_id: "v1".into(), wave: Some(0), round: 0,
                block_hash: "aabb".into(), parent_hashes: vec![],
                creator: "deadbeef".into(), weight_table_hash: None,
                outcome: "valid".into(), errors: vec![],
            }),
            TraceEvent::InsertBlock(BlockLifecycleEvent {
                node_id: "v1".into(), wave: Some(0), round: 0,
                block_hash: "aabb".into(), parent_hashes: vec![],
                creator: "deadbeef".into(), weight_table_hash: None,
            }),
            TraceEvent::BufferBlock(BlockLifecycleEvent {
                node_id: "v1".into(), wave: None, round: 1,
                block_hash: "ccdd".into(), parent_hashes: vec!["aabb".into()],
                creator: "deadbeef".into(), weight_table_hash: None,
            }),
            TraceEvent::ResolveMissingParent(ResolveMissingParentEvent {
                node_id: "v1".into(), block_hash: "ccdd".into(),
                resolved_parent_hash: "aabb".into(),
            }),
            TraceEvent::DetectEquivocation(DetectEquivocationEvent {
                node_id: "v2".into(), equivocator: "deadbeef".into(), round: 0,
                conflicting_block_hashes: vec!["aabb".into(), "1122".into()],
            }),
            TraceEvent::AcceptApproval(AcceptApprovalEvent {
                node_id: "v2".into(), wave: Some(1),
                approver_hash: "ccdd".into(), target_hash: "aabb".into(),
            }),
            TraceEvent::BuildThresholdCertificate(ThresholdCertificateEvent {
                node_id: "v1".into(), wave: 1, leader_hash: "aabb".into(),
                certificate_id: "cert01".into(), approver_count: 3,
                approver_weight: Some(300u64),
            }),
            TraceEvent::ComputeFinality(ComputeFinalityEvent {
                node_id: "v1".into(), wave: 1, block_hash: "aabb".into(),
                decision: "finalized".into(), certificate_id: Some("cert01".into()),
                output_prefix_hash: Some("ffee".into()),
            }),
            TraceEvent::RunTauOrder(TauOrderEvent {
                node_id: "v1".into(), wave: 1,
                latest_leader_hash: "aabb".into(), output_len: 5,
            }),
            TraceEvent::EmitOutput(EmitOutputEvent {
                node_id: "v1".into(), wave: 1, block_hash: "aabb".into(),
                output_index: 0, output_prefix_hash: "ffee".into(),
            }),
            TraceEvent::SendPackage(PackageEvent {
                node_id: "v1".into(), peer_id: "v2".into(),
                block_hashes: vec!["aabb".into()],
            }),
            TraceEvent::DeliverPackage(PackageEvent {
                node_id: "v2".into(), peer_id: "v1".into(),
                block_hashes: vec!["aabb".into()],
            }),
            TraceEvent::SchedulerTick(SchedulerTickEvent {
                node_id: "v1".into(), timestamp_ms: 1_000_000, wave: Some(1),
            }),
            TraceEvent::RunWaveTask(WaveTaskEvent {
                node_id: "v1".into(), wave: 1, task: "propose".into(),
            }),
        ];

        for event in events {
            let json = serde_json::to_string(&event).expect("serialize failed");
            assert!(json.contains(r#""event""#), "Missing 'event' tag in: {}", json);
            let _: TraceEvent = serde_json::from_str(&json).expect("deserialize failed");
        }
    }

    #[test]
    fn hex_produces_lowercase_even_length_string() {
        let h = hex(&[0xde, 0xad, 0xbe, 0xef]);
        assert_eq!(h, "deadbeef");
        assert_eq!(h.len(), 8);
    }

    #[test]
    fn weight_table_hash_is_deterministic() {
        use crate::types::NodeId;
        use std::collections::HashMap;

        let mut bonds: HashMap<NodeId, u64> = HashMap::new();
        bonds.insert(NodeId(vec![1]), 100);
        bonds.insert(NodeId(vec![2]), 200);
        bonds.insert(NodeId(vec![3]), 300);

        let h1 = weight_table_hash(&bonds);
        let h2 = weight_table_hash(&bonds);
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 64);
    }
}
