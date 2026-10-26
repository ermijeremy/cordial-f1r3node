# Penalty-aware PoR transition

Issue [#283](https://github.com/iCog-Labs-Dev/cordial-f1r3node/issues/283)
formalizes the state-changing boundary that applies authorized equivocation
events to a Proof-of-Reputation snapshot. The model is in
`lean/LeanVerification/SlashingTransition.lean`.

## Model

`ValidatorReputation` records active reputation, retained reputation, and the
permanent-exclusion bit for one validator. `PenaltyReputationState` adds the
round, the unique validator identities, and their accounts. Its
`WellFormed` predicate requires unique identities and zero active reputation
for every excluded key.

```lean
structure ValidatorReputation where
  activeReputation : Nat
  retainedReputation : Nat
  excluded : Bool

structure PenaltyReputationState where
  round : Nat
  validatorIds : List NodeId
  account : NodeId → ValidatorReputation

def PenaltyReputationState.WellFormed
    (state : PenaltyReputationState) : Prop
```

`AuthorizedEquivocationEvent` is intentionally distinct from
`RawEquivocationEvidence`. The `ofAuthorizedPenaltyEvent` projection accepts
only the authorization-boundary value defined by the evidence model. The
transition retains serialized evidence because Rust independently rejects an
empty proof at this layer.

`ValidPenaltyEvents` checks the successor round, stable validator identities,
unique offenders, nonempty evidence, known and active offenders, one-round
inactivity, and absence of overlap across penalty kinds.

`previousActiveTotal` and `previousCorrelatedWeightFor` read only the previous
snapshot. Therefore neither blended candidate weights nor event order can
affect correlation-tier selection.

`calculatePenaltyTransition` returns `Except PenaltyTransitionError State`.
It exposes the staged `penaltySuccessor` only after event validation and all
fixed-width arithmetic preconditions pass. `commitPenaltyTransition` models
the state-level atomic commit: either the complete successor is installed or
the complete current state is returned unchanged.

## Safety theorems

- `slash_zeroes_activeReputation` and `slash_setsExcluded` show that every
  valid slash permanently removes the offender's active voting weight.
- `isolatedSlash_setsRetainedReputation` connects the below-threshold tier to
  the base-penalty retained balance proved in `SlashingArithmetic.lean`.
- `correlatedSlash_zeroesRetainedReputation` connects the above-threshold tier
  to a full slash and zero retained balance.
- `slash_preserves_nonOffenders` proves that active innocent accounts retain
  the pre-penalty candidate value.
- `excluded_persistent` and `retainedReputation_persistent` prove that later
  candidates cannot resurrect an excluded key or replace its retained balance.
- `penaltySuccessor_wellFormed` proves that a transition preserves the state
  representation invariants.
- `invalidEvents_preserve_entireState` and
  `arithmeticFailure_preserves_entireState` cover the complete state rather
  than a single account field.
- `duplicateOffender_rejected`, `overlappingPenalty_rejected`,
  `unknownOffender_rejected`, `alreadyExcluded_rejected`, and
  `emptyEquivocationEvidence_rejected` establish fail-closed event handling.
- `eventPermutation_invariant` proves that any permutation of the authorized
  equivocation list produces the identical complete successor state.

The module also contains executable examples for the isolated and correlated
tiers, preservation of an innocent validator, every required rejection case,
reversed event order, and an attempted later restoration of an ejected key.

## Rust correspondence

| Lean definition or theorem | Rust behavior justified |
| --- | --- |
| `ValidPenaltyEvents` | `transition::apply_reputation_penalties` pre-mutation validation |
| `previousActiveTotal`, `previousCorrelatedWeightFor` | `transition::apply_reputation_penalties` previous-vector correlation aggregation |
| `isolatedSlash_setsRetainedReputation` | `penalties::compute_slash_penalty_wide` and `apply_slash_to_reputation` base tier |
| `correlatedSlash_zeroesRetainedReputation` | full tier in `compute_slash_penalty_wide` and `apply_slash_to_reputation` |
| `slash_zeroes_activeReputation`, `slash_setsExcluded` | offender updates in `transition::apply_reputation_penalties` |
| `excluded_exportsZeroWeight` | `weights::authorized_validator_weights` |
| `excluded_persistent`, `retainedReputation_persistent` | persistence logic in `audit::replay_reputation_transition_with_penalties` and `state::apply_reputation_vector` |
| `invalidEvents_preserve_entireState`, `arithmeticFailure_preserves_entireState` | staged clone in `apply_reputation_penalties` and audited atomic commit in `ReputationState` |
| rejection theorems | duplicate, overlap, unknown, empty-evidence, and already-ejected checks in `apply_reputation_penalties` |
| `eventPermutation_invariant` | canonical, order-independent penalty replay |

All declarations are proved without `sorry` or additional axioms.
