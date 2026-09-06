#![cfg(feature = "trace")]

use std::collections::HashSet;

use cordial_miners_core::NodeId;
use cordial_miners_core::simulation::adversary::{AdversarialNetwork, BlockFactory};
use cordial_miners_core::trace::TraceEvent;

fn node(id: u8) -> NodeId {
    NodeId(vec![id])
}

/// Exercise the real scheduler, transport, validation, buffer, resolution and
/// wave-task paths.  Synthetic events belong only in the schema round-trip
/// test; this test proves these variants are emitted at their runtime sites.
#[test]
fn runtime_emits_dissemination_and_scheduler_events() {
    let path = std::env::temp_dir().join(format!(
        "cordial-runtime-trace-{}-{}.json",
        std::process::id(),
        std::thread::current().name().unwrap_or("test")
    ));
    let _ = std::fs::remove_file(&path);

    // This integration-test binary contains one test, so its process-local
    // trace-sink environment cannot race another test thread.
    unsafe { std::env::set_var("CORDIAL_TRACE_FILE", &path) };

    let recipient = node(1);
    let mut network = AdversarialNetwork::equal_stake(2);
    let mut factory = BlockFactory::new();
    let parent = factory.block(&node(1), HashSet::new());
    let child = factory.block(&node(2), HashSet::from([parent.identity.clone()]));

    // Force the actual missing-parent lifecycle: child buffers, parent arrives,
    // then retry emits one resolution and inserts the child.
    network.send_to(&child, std::slice::from_ref(&recipient));
    network.deliver_ready();
    network.send_to(&parent, std::slice::from_ref(&recipient));
    network.deliver_ready();
    network.retry_all_buffers();
    network.advance(1);

    let observer = network.node(&recipient).expect("recipient exists");
    let _ = observer.latest_weighted_final_leader(3, |_| Some(node(1)));

    unsafe { std::env::remove_var("CORDIAL_TRACE_FILE") };
    let content = std::fs::read_to_string(&path).expect("runtime trace was written");
    let _ = std::fs::remove_file(&path);
    let events: Vec<TraceEvent> = content
        .lines()
        .map(|line| serde_json::from_str(line).expect("runtime event is valid JSON"))
        .collect();

    assert!(
        events
            .iter()
            .any(|event| matches!(event, TraceEvent::SendPackage(_)))
    );
    assert!(
        events
            .iter()
            .any(|event| matches!(event, TraceEvent::DeliverPackage(_)))
    );
    assert!(
        events
            .iter()
            .any(|event| matches!(event, TraceEvent::ValidateBlock(_)))
    );
    assert!(
        events
            .iter()
            .any(|event| matches!(event, TraceEvent::BufferBlock(_)))
    );
    assert!(
        events
            .iter()
            .any(|event| matches!(event, TraceEvent::ResolveMissingParent(_)))
    );
    assert!(
        events
            .iter()
            .any(|event| matches!(event, TraceEvent::InsertBlock(_)))
    );
    assert!(
        events
            .iter()
            .any(|event| matches!(event, TraceEvent::SchedulerTick(_)))
    );
    assert!(
        events
            .iter()
            .any(|event| matches!(event, TraceEvent::RunWaveTask(_)))
    );
}
