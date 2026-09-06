# 05b — Proof-to-test mapping

Issue #188 is a conformance system, not merely a JSON parser. The implemented
dependency chain is:

```text
KR1 Blocklace / KR2 Equivocation+Approval / KR4 Finality+Ordering
                              ↓
                    executable CMRef predicates
                              ↓
                      strict replay adapter
                              ↓
                    compare with Rust result
```

## Mapping table

| Rust behavior | Trace event | Lean CMRef/replay calculation | Formal property/theorem | Positive test | Negative oracle |
|---|---|---|---|---|---|
| block insertion | `InsertBlock` | resolve parents, construct `Block`, `blocklaceInsert`, retain `ValidBlocklace` proof | KR1 `ValidBlocklace.insert`, closure | all three | missing predecessor |
| equivocation | `DetectEquivocation` | `CMRef.checkEquivocation` | KR2 `Equivocation`; `checkEquivocation_iff` | equivocation | false creator/round/block cases |
| approval | `AcceptApproval` | `CMRef.checkApproves` | KR2 `Approves`; `checkApproves_iff` | all three | invalid evidence rejected through CMRef/certificate checks |
| weighted quorum | certificate fields | recompute validator ids, support, total and strict 2/3 | `StrictTwoThirdsMaj`; `checkStrictTwoThirds_iff` | normal/equivocation | insufficient quorum, low stake |
| ratification certificate | `BuildThresholdCertificate(kind=ratification)` | `CMRef.checkRatifies` plus evidence/id/hash checks | `Ratifies`; `checkRatifies_iff` | normal/equivocation | invalid certificate/id |
| super-ratification certificate | `BuildThresholdCertificate(kind=super_ratification)` | `CMRef.checkSuperRatifies` | `SuperRatifies`; `checkSuperRatifies_iff` | normal/equivocation | insufficient quorum/invalid certificate |
| finality | `ComputeFinality` | `CMRef.checkFinal`, independent of `decision` | KR4 `FinalLeader`; `checkFinal_iff` | all three | flipped decision and weakened-threshold mutation |
| ordering | `RunTauOrder` | `CMRef.computeTau` over formal DAG using CMRef finality, ratification and approval | KR4 ordering algorithm; abstract prefix theorem remains documented boundary | normal | incorrect τ order |
| output | `EmitOutput` | index into Lean τ and recompute running FNV prefix | exact τ output prefix | normal | incorrect block/index/prefix |
| weights | every weighted decision | parse table, canonical encode, recompute hash | `bondOf`, `StrictTwoThirdsMaj` | all three | wrong table hash |

## Finality oracle

The critical comparison in `Replay.lean` is logically:

```text
trace block/parents/creator + sidecar weights/leaders
                         ↓
               formal ValidBlocklace
                         ↓
                 CMRef.checkFinal
                         ↓ checkFinal_iff
                    FinalLeader
                         ↓
        Lean Bool == Rust decision string
```

`checkFinal_iff` is proved without `sorry` or a replacement axiom. Its lower
layers likewise have executable-to-Prop equivalence theorems. Therefore
`"finalized"` is parsed only as Rust's claimed result; it is never sufficient
for acceptance.

## Fixture obligations

The positive runner also rejects vacuous or truncated scenarios:

- normal must contain approvals, certificates, a positive finality decision,
  τ, and a complete non-empty output;
- equivocation must contain a valid equivocation and retain finality;
- low stake must contain approvals and only negative weighted finality;
- every replay must end without unresolved buffers or a partial τ output.

`conformance_tests.lean` mutates parsed real traces in memory, keeping the
expected answer independent in CMRef. It covers invalid finality, insufficient
quorum, invalid certificate, false equivocation, missing predecessor, wrong τ,
wrong output prefix, wrong weight hash, and a simulated `> 1/2` Rust threshold.
