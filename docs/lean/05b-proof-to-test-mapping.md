# 05b — Proof-to-test mapping

Issue #188 connects the previously proved KR layers to executable replay. It
does not treat a Rust result field as an oracle:

```text
KR1 Blocklace → KR2 observation/equivocation → KR3 weight certificate
       → KR4 approval/ratification/finality/order
       → executable CMRef → replayed Rust observation
```

Source references below use `file::declaration` or `file::function`; these are
more stable than line numbers while remaining exact and searchable.

## End-to-end behavior map

| Protocol behavior | Formal predicate/theorem | Executable CMRef/replay | Rust implementation | Runtime fixture/test | Trace event |
|---|---|---|---|---|---|
| content-addressed block | `Block.lean::Block.id_eq`, `hashContent`, `hashInj` | `Replay.lean::insertBlock` constructs `id := hashContent creator content` and proves `id_eq := rfl` | `block.rs::Block`, `crypto.rs::hash_content` | every canonical fixture | `create_block`, `insert_block` |
| predecessor-closed insertion | `Blocklace.lean::Closed`, `Insertable`, `insertPreservesClosed`, `insertRequiresPredecessors`; `Observe.lean::closed_of_valid` | `ReplayDag.blocklace` plus a retained `ValidBlocklace` proof after every insertion | `blocklace.rs::insert`, `commit_validated` | `test_blocklace::block_with_known_predecessor_can_be_inserted`; negative `bad-closure` | `insert_block` |
| buffering all missing parents | same KR1 closure obligation | replay recomputes the complete absent-parent set and tracks each resolution | `simulation/dissemination.rs::SimNode::receive_block`, `retry_buffered_blocks` | `trace_runtime_instrumentation::runtime_emits_dissemination_and_scheduler_events` | `buffer_block`, `resolve_missing_parent` |
| observation closure | `Observe.lean::Observes`, `observeSet_sound`, `observeSet_complete`, `observeSet_equiv` | `CMRef.lean::checkObserves`; `checkObserves_iff` | `Blocklace::observe`, `consensus::cordiality::observed_block_ids` | `test_blocklace::test_observe_includes_self_and_ancestors`; approval/certificate fixtures | approval/certificate evidence |
| same-round equivocation | `Equivocation.lean::Fork`, `Equivocation`; `same_depth_incomparable` | `CMRef.lean::checkEquivocation`; `checkEquivocation_iff` | `cordiality.rs::all_equivocations` | `equivocation`; `test_cordiality::detects_same_round_equivocation`; negative `false-equivocation` | `detect_equivocation` |
| exclusion after acknowledging a fork | `Acknowledges`, `VouchesFor`, `equivocation_exclusion`, `equivocation_not_approved`; `Approval.lean::approves_exclusion` | `checkApproves` enumerates the finite DAG and rejects observed conflicting branches | `approval.rs::approves_with_memo` | `test_approval::rejects_target_with_observed_equivocating_sibling`; `equivocation` | `accept_approval` |
| approval | `Approval.lean::Approves` | `CMRef.lean::ApprovesFinite`, `checkApproves`; `checkApproves_iff` | `approval.rs::approves`, `weighted_approving_creators_with_memo` | all fixtures; `test_approval::*` | `accept_approval` |
| deduplicated certificate accumulation | `WCert.lean::WCert.Invariant`, `empty_invariant`, `accept_invariant` | `CMRef.lean::buildWCert`; `buildWCert_invariant` | distinct-creator collection in `cordiality.rs::weighted_ratifies_with_memo` | normal/equivocation; duplicate member negative | `build_threshold_certificate` |
| exact weighted quorum | `Approval.lean::StrictTwoThirdsMaj`; `Weights.lean::strict_two_thirds_iff_openTheta` | `CMRef.lean::checkStrictTwoThirds`; `checkStrictTwoThirds_iff` | `cordiality.rs::strict_two_thirds`, integer predicate `3*s > 2*t` | normal/equivocation/low-stake; `weighted_supermajority_is_strictly_more_than_two_thirds`; real mutation script | certificate/finality events |
| ratification | `Approval.lean::Ratifies`, `ratifies_mono` | `CMRef.lean::approvingCreators`, `checkRatifies`; `checkRatifies_iff` | `cordiality.rs::weighted_ratifies_with_memo` | normal/equivocation; `test_weighted_ratification::weighted_ratifies_*`; invalid-certificate negative | `build_threshold_certificate` with `kind=ratification` |
| super-ratification | `Approval.lean::SuperRatifies`, `superRatifies_mono` | `CMRef.lean::ratifyingCreators`, `checkSuperRatifies`; `checkSuperRatifies_iff` | `cordiality.rs::weighted_super_ratifies_with_memo` | normal/equivocation; `test_weighted_ratification::weighted_super_ratifies_*`; invalid-quorum negative | `build_threshold_certificate` with `kind=super_ratification` |
| leader selection and finality | `Finality.lean::leaderBlocksOfWave`, `FinalLeader`, `leaderBlocks_equivocation`, `no_conflicting_finals` | `CMRef.lean::waveWitness`, `checkFinal`; `checkFinal_iff` | `finality.rs::is_weighted_final_leader`, `latest_weighted_final_leader` | all fixtures; `test_finality::weighted_*`; invalid-finality negative | `compute_finality` |
| canonical tau ordering | `Ordering.lean::SubBlocklace`, `observes_of_subBlocklace`, `FinalLeader_of_subBlocklace`; abstract `tau` contract | `CMRef.lean::computeTau` reuses `checkFinal`, `checkRatifies`, `checkApproves`, then deterministic topological order | `ordering.rs::weighted_tau`, `weighted_tau_from_leader`, `xsort` | normal; `test_ordering::weighted_tau_*`; bad-tau negative | `run_tau_order` |
| emitted output prefix | tau result above | replay indexes the Lean order and recomputes `computeOutputPrefixHash` | `ordering.rs::emit_weighted_checkpoint_prefix`, `trace.rs::output_prefix_hash` | normal; bad-output-prefix negative | `emit_output` |
| validator configuration | `ValidBonds`, `bondOf`, `StrictTwoThirdsMaj` | `Replay.lean::validateConfig`, `computeWeightTableHash`, `ReplayConfig.bonds` | fixture `ReplayConfig`; `trace.rs::weight_table_hash` | every fixture; wrong-weight-table negative | `weight_table_hash` fields plus sidecar |

## Formal dependency inventory

This inventory records how the earlier proofs feed the safety-facing bridge.
Proof-internal lemmas do not each need a separate event; they discharge a
premise of a mapped theorem.

| Formal source | Declarations used by the conformance chain | Consumer |
|---|---|---|
| `Block.lean` | `Block.id_eq`, `hashContent`, `hashInj` | replay construction and collision exclusion |
| `Blocklace.lean` | `Closed`, `Insertable`, `blocklaceInsert`, `insertPreservesClosed`, `insertRequiresPredecessors`, `ValidBlocklace.insert` | `ReplayDag` insertion |
| `Observe.lean` | `DirectPred`, `Observes`, `observes_refl/step/trans`, `closed_of_valid`, `directPred_insert_*`, `directPred_acc`, `directPred_wf_of_valid`, `directPred_acyclic`, `observes_antisymm`, `observes_partialOrder`, `observes_mono`, `observeSetWF`, `observeSetWF_eq`, `observeSet_sound/complete/equiv`, `Precedes`, `precedes_implies_observes` | finite `observeSet`; all approval/equivocation/finality calculations |
| `Equivocation.lean` | `creatorOf`, `blockDepthWF`, `blockDepthWF_eq`, `blockDepth`, `blockDepth_directPred`, `depth_strict_of_precedes`, `same_depth_incomparable`, `Fork`, `Equivocation`, `Equivocator`, `HonestIn`, `honest_chain_linearity`, `honest_not_equivocator`, `Acknowledges`, `Hides`, `CandidateAcknowledges`, `candidateAcknowledges_of_inserted`, `acknowledgement_monotone`, `VouchesFor`, `equivocation_exclusion`, `equivocation_not_approved` | `checkEquivocation`, `checkApproves`, and finality safety |
| `Weights.lean` | `wt_le_totalWeight`, `wt_union_add_wt_inter`, `wt_add_wt_compl`, `weighted_overlap`, `n_twinedness_theta`, `openF_inter`, `n_twinedness_F`, `honest_triple_intersection`, `strict_two_thirds_iff_openTheta` | arithmetic foundation and the finite `Approval.lean` quorum results |
| `WCert.lean` | `WCert.Invariant`, `WCert.empty`, `WCert.accept`, `WCert.empty_invariant`, `WCert.accept_invariant` | `buildWCert` and `buildWCert_invariant` during certificate replay |
| `Approval.lean` | `Approves`, `ValidBonds`, `StrictTwoThirdsMaj`, `bondOf_*`, `finset_honest_triple_intersection`, `Ratifies`, `SuperRatifies`, `approves_implies_vouchesFor`, `approves_exclusion`, `ratifies_mono`, `superRatifies_mono` | executable approval/quorum/certificate layers and `no_conflicting_finals` |
| `Finality.lean` | `waveOfRound`, `leaderRoundOfWave`, `lastRoundOfWave`, `waveOfRound_leaderRound`, `leaderRound_le_lastRound`, `leaderBlocksOfWave`, `leaderBlocks_equivocation`, `FinalLeader`, `no_conflicting_finals` | `checkFinal` and finality replay |
| `Ordering.lean` | `SubBlocklace`, `observes_of_subBlocklace`, `FinalLeader_of_subBlocklace`, abstract `tau`, `tau_prefix_monotone` | ordering specification and the explicitly documented trust boundary below |

The concrete demonstration theorems in the second half of
`Equivocation.lean` prove the same definitions on a small witness DAG; they
remain compile-time regression examples and are not substituted for replaying
the Rust fixtures.

## Executable-to-Prop bridge

The critical chain is:

```text
trace block/parent/creator data + independently loaded weights/leaders
                              ↓
                 proof-valid formal Blocklace
                              ↓
      checkApproves / checkRatifies / checkSuperRatifies
                              ↓
                       checkFinal
                              ↓ checkFinal_iff
                       FinalLeader
                              ↓
                 compare with Rust decision
```

The seven consensus bridge theorems are `checkObserves_iff`,
`checkEquivocation_iff`, `checkApproves_iff`,
`checkStrictTwoThirds_iff`, `checkRatifies_iff`,
`checkSuperRatifies_iff`, and `checkFinal_iff`. Certificate accumulation adds
`buildWCert_invariant`. None is an axiom or contains `sorry`.

## Ordering trust boundary

The earlier KR4 module exposes abstract `Ordering.lean::tau` and assumes
`tau_prefix_monotone`. That axiom is not used as an executable oracle and this
PR does not claim to prove it. `CMRef.computeTau` is the executable refinement:
it selects leaders using proved `checkFinal`, recursively selects prior leaders
with proved `checkRatifies`, filters with proved `checkApproves`, and performs a
deterministic topological sort. Replay compares every reported ordered hash and
then every emitted output item. The negative tau and output tests establish
that the comparison is not unconditional acceptance.

## Non-vacuity and negative oracles

The positive runner requires scenario-specific evidence so a truncated trace
cannot pass: normal needs approval, certificate, positive finality, tau, and a
complete output; equivocation needs a validated equivocation and safe finality;
low-stake needs approval evidence and only negative weighted finality.

`lean/conformance_tests.lean` independently rejects malformed JSON, unknown
events, null/zero confusion, missing closure, false finality, insufficient
quorum, wrong certificates, false equivocation, tau mismatch, output-prefix
mismatch, and weight-table mismatch. The separate
`scripts/issue188_mutation_test.sh` compiles and executes genuinely weakened
Rust quorum code; it does not derive or edit the expected result from the
trace.
