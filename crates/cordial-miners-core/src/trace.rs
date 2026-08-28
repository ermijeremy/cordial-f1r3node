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