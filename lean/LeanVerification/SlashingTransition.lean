/-
Penalty-aware Proof-of-Reputation state transitions.

This module models the state-changing boundary in `cordial-por`: callers may
submit only already-authorized equivocation events, validation is performed
against the complete previous snapshot, and a successor is exposed only after
validation and arithmetic preconditions have succeeded.  Correlation tiers
are computed exclusively from previous-round active reputation.
-/

import Mathlib
import LeanVerification.SlashingArithmetic

namespace CordialMiners

/-! ## Reputation state and exported weight -/

/-- The three reputation fields stored for one validator key. -/
structure ValidatorReputation where
  activeReputation : Nat
  retainedReputation : Nat
  excluded : Bool
  deriving DecidableEq, Repr

/-- The complete penalty-relevant PoR state.

`validatorIds` is the modeled counterpart of the canonically ordered Rust
entry list.  Keeping lookup as a function makes the transition definitions
pointwise and prevents accidental insertion of a validator by a penalty.
-/
structure PenaltyReputationState where
  round : Nat
  validatorIds : List NodeId
  account : NodeId → ValidatorReputation

/-- State invariants enforced by Rust's canonical entry validation. -/
def PenaltyReputationState.WellFormed (state : PenaltyReputationState) : Prop :=
  state.validatorIds.Nodup ∧
    ∀ id, id ∈ state.validatorIds →
      (state.account id).excluded = true →
        (state.account id).activeReputation = 0

/-- Consensus weight exported for an authorized identity.

Unknown and permanently excluded keys both fail closed to zero in this pure
projection.  The Rust wrapper additionally rejects missing identities and a
zero total authorized weight.
-/
def exportedActiveWeight (state : PenaltyReputationState) (id : NodeId) : Nat :=
  if id ∈ state.validatorIds then
    if (state.account id).excluded then 0 else (state.account id).activeReputation
  else
    0

theorem excluded_exportsZeroWeight
    (state : PenaltyReputationState) (id : NodeId)
    (hExcluded : (state.account id).excluded = true) :
    exportedActiveWeight state id = 0 := by
  simp [exportedActiveWeight, hExcluded]

/-! ## Authorized transition inputs -/

/-- Transition-layer view of an event that has crossed the authorization
boundary modeled by `AuthorizedPenaltyEvent` in `Slashing.lean`.

This is intentionally a different type from `RawEquivocationEvidence`.
`evidence` remains present because the Rust transition independently rejects
an empty serialized proof even after authorization.
-/
structure AuthorizedEquivocationEvent where
  offender : NodeId
  evidence : List UInt8
  offenseRound : Nat
  applicationRound : Nat
  deriving DecidableEq, Repr

/-- Project the full evidence/crypto/policy authorization object into the
fields consumed by the penalty transition. -/
def AuthorizedEquivocationEvent.ofAuthorizedPenaltyEvent
    (B : Blocklace) (hV : ValidBlocklace B)
    (crypto : CryptographicVerificationAssumption)
    (policy : PenaltyAuthorizationPolicy)
    (event : AuthorizedPenaltyEvent B hV crypto policy) :
    AuthorizedEquivocationEvent where
  offender := event.offender
  evidence := event.evidence.proofMaterial
  offenseRound := event.offenseRound
  applicationRound := event.applicationRound

/-- Inactivity is included to model cross-penalty overlap rejection.  Its
reputation decay is outside the slashing invariants proved by this module. -/
structure TransitionInactivityEvent where
  offender : NodeId
  missedRounds : Nat
  deriving DecidableEq, Repr

/-- Finalized penalty events presented for exactly one successor round. -/
structure PenaltyTransitionEvents where
  round : Nat
  equivocations : List AuthorizedEquivocationEvent
  inactivity : List TransitionInactivityEvent
  deriving DecidableEq, Repr

def allPenaltyOffenders (events : PenaltyTransitionEvents) : List NodeId :=
  events.equivocations.map (·.offender) ++ events.inactivity.map (·.offender)

/-- All structural validation performed before any state update becomes
visible.  In particular, every offender is looked up in the previous state,
and an already-ejected key can never be penalized or reactivated. -/
def ValidPenaltyEvents
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents) : Prop :=
  events.round = previous.round + 1 ∧
    candidate.round = events.round ∧
    candidate.validatorIds = previous.validatorIds ∧
    (allPenaltyOffenders events).Nodup ∧
    events.equivocations.Forall (fun event =>
      event.applicationRound = events.round ∧
      event.evidence ≠ [] ∧
      event.offender ∈ previous.validatorIds ∧
      (previous.account event.offender).excluded = false) ∧
    events.inactivity.Forall (fun event =>
      event.missedRounds = 1 ∧
      event.offender ∈ previous.validatorIds ∧
      (previous.account event.offender).excluded = false)

instance instDecidableValidPenaltyEvents
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents) :
    Decidable (ValidPenaltyEvents previous candidate events) := by
  unfold ValidPenaltyEvents
  infer_instance

/-! ## Previous-round correlation and staged successor -/

/-- Sum of all active previous-round reputation.  Excluded entries contribute
zero, matching the Rust `filter(|entry| !entry.is_excluded)` aggregation. -/
def previousActiveTotal (state : PenaltyReputationState) : Nat :=
  ∑ id ∈ state.validatorIds.toFinset,
    if (state.account id).excluded then 0 else (state.account id).activeReputation

def isEquivocationOffender
    (events : Finset AuthorizedEquivocationEvent) (id : NodeId) : Bool :=
  decide (∃ event ∈ events, event.offender = id)

/-- Correlated weight for `id`'s offense round, using only previous-round
active weights.  Valid input has one event per offender, so the outer sum has
exactly one term.  Defining it over a `Finset` also makes event order
irrelevant by construction. -/
def previousCorrelatedWeightFor
    (previous : PenaltyReputationState)
    (events : Finset AuthorizedEquivocationEvent)
    (id : NodeId) : Nat :=
  ∑ target ∈ events.filter (fun event => event.offender = id),
    ∑ event ∈ events.filter (fun event => event.offenseRound = target.offenseRound),
      if (previous.account event.offender).excluded then
        0
      else
        (previous.account event.offender).activeReputation

private def slashedAccount
    (config : SlashingConfig)
    (previous : PenaltyReputationState)
    (events : Finset AuthorizedEquivocationEvent)
    (id : NodeId) : ValidatorReputation :=
  let old := previous.account id
  let penalty := selectSlashPenalty config
    (previousCorrelatedWeightFor previous events id)
    (previousActiveTotal previous)
  { activeReputation := 0
    retainedReputation := retainedReputation config old.activeReputation penalty
    excluded := true }

/-- Pure staged successor.  Existing exclusions take priority over the new
candidate snapshot, so neither ratings nor later direct assignment can restore
an ejected key. -/
def penaltySuccessor
    (config : SlashingConfig)
    (previous candidate : PenaltyReputationState)
    (round : Nat)
    (events : Finset AuthorizedEquivocationEvent) : PenaltyReputationState where
  round := round
  validatorIds := previous.validatorIds
  account := fun id =>
    if (previous.account id).excluded then
      previous.account id
    else if isEquivocationOffender events id then
      slashedAccount config previous events id
    else
      candidate.account id

/-- Explicit preconditions for the checked fixed-width Rust arithmetic.
Failure of any clause rejects the staged transition rather than exposing a
partially updated state. -/
def PenaltyArithmeticReady
    (config : SlashingConfig)
    (previous : PenaltyReputationState)
    (events : Finset AuthorizedEquivocationEvent) : Prop :=
  config.WellFormed ∧
    config.FitsU64 ∧
    0 < previousActiveTotal previous ∧
    previousActiveTotal previous ≤ u128Max ∧
    previousActiveTotal previous * config.scale ≤ u128Max ∧
    previousActiveTotal previous * config.correlationThreshold ≤ u128Max ∧
    (∀ event ∈ events,
      previousCorrelatedWeightFor previous events event.offender ≤
        previousActiveTotal previous ∧
      (previous.account event.offender).activeReputation ≤ u64Max ∧
      (previous.account event.offender).activeReputation * config.scale ≤ u128Max)

instance instDecidablePenaltyArithmeticReady
    (config : SlashingConfig)
    (previous : PenaltyReputationState)
    (events : Finset AuthorizedEquivocationEvent) :
    Decidable (PenaltyArithmeticReady config previous events) := by
  unfold PenaltyArithmeticReady
  infer_instance

inductive PenaltyTransitionError where
  | invalidEvents
  | arithmeticFailure
  deriving DecidableEq, Repr

/-- Validate and calculate without mutating the caller's current state. -/
def calculatePenaltyTransition
    (config : SlashingConfig)
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents) :
    Except PenaltyTransitionError PenaltyReputationState :=
  if ValidPenaltyEvents previous candidate events then
    let eventSet := events.equivocations.toFinset
    if PenaltyArithmeticReady config previous eventSet then
      .ok (penaltySuccessor config previous candidate events.round eventSet)
    else
      .error .arithmeticFailure
  else
    .error .invalidEvents

/-- Atomic state-level commit.  Any validation or arithmetic error returns the
entire prior state, including its round, validator set, retained balances, and
exclusion flags. -/
def commitPenaltyTransition
    (config : SlashingConfig)
    (current candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents) : PenaltyReputationState :=
  match calculatePenaltyTransition config current candidate events with
  | .ok successor => successor
  | .error _ => current

/-! ## Slashing and atomicity invariants -/

theorem slash_zeroes_activeReputation
    (config : SlashingConfig)
    (previous candidate : PenaltyReputationState)
    (round : Nat) (events : Finset AuthorizedEquivocationEvent)
    (id : NodeId)
    (hActive : (previous.account id).excluded = false)
    (hOffender : isEquivocationOffender events id = true) :
    ((penaltySuccessor config previous candidate round events).account id
      ).activeReputation = 0 := by
  simp [penaltySuccessor, hActive, hOffender, slashedAccount]

theorem slash_setsExcluded
    (config : SlashingConfig)
    (previous candidate : PenaltyReputationState)
    (round : Nat) (events : Finset AuthorizedEquivocationEvent)
    (id : NodeId)
    (hActive : (previous.account id).excluded = false)
    (hOffender : isEquivocationOffender events id = true) :
    ((penaltySuccessor config previous candidate round events).account id
      ).excluded = true := by
  simp [penaltySuccessor, hActive, hOffender, slashedAccount]

theorem isolatedSlash_setsRetainedReputation
    (config : SlashingConfig)
    (previous candidate : PenaltyReputationState)
    (round : Nat) (events : Finset AuthorizedEquivocationEvent)
    (id : NodeId)
    (hActive : (previous.account id).excluded = false)
    (hOffender : isEquivocationOffender events id = true)
    (hIsolated : atOrBelowCorrelationThreshold config
      (previousCorrelatedWeightFor previous events id)
      (previousActiveTotal previous)) :
    ((penaltySuccessor config previous candidate round events).account id
      ).retainedReputation =
        retainedReputation config (previous.account id).activeReputation
          config.basePenalty := by
  simp [penaltySuccessor, hActive, hOffender, slashedAccount,
    selectSlashPenalty_eq_base _ _ _ hIsolated]

theorem correlatedSlash_zeroesRetainedReputation
    (config : SlashingConfig)
    (previous candidate : PenaltyReputationState)
    (round : Nat) (events : Finset AuthorizedEquivocationEvent)
    (id : NodeId)
    (hConfig : config.WellFormed)
    (hActive : (previous.account id).excluded = false)
    (hOffender : isEquivocationOffender events id = true)
    (hCorrelated : ¬ atOrBelowCorrelationThreshold config
      (previousCorrelatedWeightFor previous events id)
      (previousActiveTotal previous)) :
    ((penaltySuccessor config previous candidate round events).account id
      ).retainedReputation = 0 := by
  simp [penaltySuccessor, hActive, hOffender, slashedAccount,
    selectSlashPenalty_eq_scale _ _ _ hConfig hCorrelated,
    retainedReputation_full_slash]

theorem slash_preserves_nonOffenders
    (config : SlashingConfig)
    (previous candidate : PenaltyReputationState)
    (round : Nat) (events : Finset AuthorizedEquivocationEvent)
    (id : NodeId)
    (hActive : (previous.account id).excluded = false)
    (hInnocent : isEquivocationOffender events id = false) :
    (penaltySuccessor config previous candidate round events).account id =
      candidate.account id := by
  simp [penaltySuccessor, hActive, hInnocent]

theorem excluded_persistent
    (config : SlashingConfig)
    (previous candidate : PenaltyReputationState)
    (round : Nat) (events : Finset AuthorizedEquivocationEvent)
    (id : NodeId)
    (hExcluded : (previous.account id).excluded = true) :
    (penaltySuccessor config previous candidate round events).account id =
      previous.account id := by
  simp [penaltySuccessor, hExcluded]

theorem retainedReputation_persistent
    (config : SlashingConfig)
    (previous candidate : PenaltyReputationState)
    (round : Nat) (events : Finset AuthorizedEquivocationEvent)
    (id : NodeId)
    (hExcluded : (previous.account id).excluded = true) :
    ((penaltySuccessor config previous candidate round events).account id
      ).retainedReputation = (previous.account id).retainedReputation := by
  rw [excluded_persistent config previous candidate round events id hExcluded]

/-- Slashing preserves the state representation invariants when both the prior
and pre-penalty candidate snapshots are well formed. -/
theorem penaltySuccessor_wellFormed
    (config : SlashingConfig)
    (previous candidate : PenaltyReputationState)
    (round : Nat) (events : Finset AuthorizedEquivocationEvent)
    (hPrevious : previous.WellFormed)
    (hCandidate : candidate.WellFormed)
    (hIds : candidate.validatorIds = previous.validatorIds) :
    (penaltySuccessor config previous candidate round events).WellFormed := by
  constructor
  · exact hPrevious.1
  · intro id hKnown hExcluded
    change id ∈ previous.validatorIds at hKnown
    by_cases hPriorExcluded : (previous.account id).excluded = true
    · rw [excluded_persistent config previous candidate round events id hPriorExcluded]
      exact hPrevious.2 id hKnown hPriorExcluded
    · have hPriorActive : (previous.account id).excluded = false := by
        simpa using hPriorExcluded
      by_cases hOffender : isEquivocationOffender events id = true
      · exact slash_zeroes_activeReputation config previous candidate round events id
          hPriorActive hOffender
      · have hInnocent : isEquivocationOffender events id = false := by
          simpa using hOffender
        rw [slash_preserves_nonOffenders config previous candidate round events id
          hPriorActive hInnocent] at hExcluded ⊢
        exact hCandidate.2 id (by simpa [hIds] using hKnown) hExcluded

theorem invalidEvents_preserve_entireState
    (config : SlashingConfig)
    (current candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents)
    (hInvalid : ¬ ValidPenaltyEvents current candidate events) :
    commitPenaltyTransition config current candidate events = current := by
  simp [commitPenaltyTransition, calculatePenaltyTransition, hInvalid]

theorem arithmeticFailure_preserves_entireState
    (config : SlashingConfig)
    (current candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents)
    (hValid : ValidPenaltyEvents current candidate events)
    (hArithmetic : ¬ PenaltyArithmeticReady config current
      events.equivocations.toFinset) :
    commitPenaltyTransition config current candidate events = current := by
  simp [commitPenaltyTransition, calculatePenaltyTransition, hValid, hArithmetic]

theorem duplicateOffender_rejected
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents)
    (hDuplicate : ¬ (allPenaltyOffenders events).Nodup) :
    ¬ ValidPenaltyEvents previous candidate events := by
  intro hValid
  exact hDuplicate hValid.2.2.2.1

theorem unknownOffender_rejected
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents)
    (event : AuthorizedEquivocationEvent)
    (hEvent : event ∈ events.equivocations)
    (hUnknown : event.offender ∉ previous.validatorIds) :
    ¬ ValidPenaltyEvents previous candidate events := by
  intro hValid
  have hForall := hValid.2.2.2.2.1
  rw [List.forall_iff_forall_mem] at hForall
  exact hUnknown (hForall event hEvent).2.2.1

theorem emptyEquivocationEvidence_rejected
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents)
    (event : AuthorizedEquivocationEvent)
    (hEvent : event ∈ events.equivocations)
    (hEmpty : event.evidence = []) :
    ¬ ValidPenaltyEvents previous candidate events := by
  intro hValid
  have hForall := hValid.2.2.2.2.1
  rw [List.forall_iff_forall_mem] at hForall
  exact (hForall event hEvent).2.1 hEmpty

theorem overlappingPenalty_rejected
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents)
    (id : NodeId)
    (hEquivocation : id ∈ events.equivocations.map (·.offender))
    (hInactivity : id ∈ events.inactivity.map (·.offender)) :
    ¬ ValidPenaltyEvents previous candidate events := by
  intro hValid
  have hNodup := hValid.2.2.2.1
  simp only [allPenaltyOffenders, List.nodup_append] at hNodup
  exact (hNodup.2.2 id hEquivocation id hInactivity) rfl

theorem alreadyExcluded_rejected
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents)
    (event : AuthorizedEquivocationEvent)
    (hEvent : event ∈ events.equivocations)
    (hExcluded : (previous.account event.offender).excluded = true) :
    ¬ ValidPenaltyEvents previous candidate events := by
  intro hValid
  have hForall := hValid.2.2.2.2.1
  rw [List.forall_iff_forall_mem] at hForall
  have hActive := (hForall event hEvent).2.2.2
  simp [hExcluded] at hActive

/-- A valid event set is semantically unordered.  Reversing or otherwise
permuting it produces the identical complete successor state. -/
theorem eventPermutation_invariant
    (config : SlashingConfig)
    (previous candidate : PenaltyReputationState)
    (round : Nat)
    (first second : List AuthorizedEquivocationEvent)
    (hPermutation : first.Perm second) :
    penaltySuccessor config previous candidate round first.toFinset =
      penaltySuccessor config previous candidate round second.toFinset := by
  have hSets : first.toFinset = second.toFinset := by
    ext event
    simp only [List.mem_toFinset]
    exact hPermutation.mem_iff
  rw [hSets]

/-! ## Small executable scenarios -/

private def sampleAccount (id : NodeId) : ValidatorReputation :=
  if id < 4 then ⟨100, 0, false⟩ else ⟨0, 0, false⟩

private def samplePrevious : PenaltyReputationState :=
  ⟨0, [0, 1, 2, 3], sampleAccount⟩

private def sampleCandidate : PenaltyReputationState :=
  ⟨1, [0, 1, 2, 3], sampleAccount⟩

private def sampleEquivocation (id offenseRound : Nat) : AuthorizedEquivocationEvent :=
  ⟨id, [1], offenseRound, 1⟩

private def sampleInactivity (id : Nat) : TransitionInactivityEvent :=
  ⟨id, 1⟩

/-- One isolated offender among four equal validators retains 75%. -/
example :
    (penaltySuccessor defaultSlashingConfig samplePrevious sampleCandidate 1
      [sampleEquivocation 0 7].toFinset).account 0 = ⟨0, 75, true⟩ := by
  native_decide

/-- Two same-round offenders exceed the 30% threshold and retain zero. -/
example :
    (penaltySuccessor defaultSlashingConfig samplePrevious sampleCandidate 1
      [sampleEquivocation 0 7, sampleEquivocation 1 7].toFinset).account 0 =
        ⟨0, 0, true⟩ := by
  native_decide

/-- An innocent validator is unchanged alongside several offenders. -/
example :
    (penaltySuccessor defaultSlashingConfig samplePrevious sampleCandidate 1
      [sampleEquivocation 0 7, sampleEquivocation 1 7].toFinset).account 3 =
        sampleCandidate.account 3 := by
  native_decide

/-- Duplicate equivocation offenders are rejected. -/
example : ¬ ValidPenaltyEvents samplePrevious sampleCandidate
    ⟨1, [sampleEquivocation 0 7, sampleEquivocation 0 7], []⟩ := by
  native_decide

/-- Equivocation/inactivity overlap is rejected. -/
example : ¬ ValidPenaltyEvents samplePrevious sampleCandidate
    ⟨1, [sampleEquivocation 0 7], [sampleInactivity 0]⟩ := by
  native_decide

/-- An unknown offender is rejected. -/
example : ¬ ValidPenaltyEvents samplePrevious sampleCandidate
    ⟨1, [sampleEquivocation 9 7], []⟩ := by
  native_decide

private def excludedPrevious : PenaltyReputationState :=
  { samplePrevious with
    account := fun id => if id = 0 then ⟨0, 75, true⟩ else sampleAccount id }

/-- An already-ejected offender is rejected. -/
example : ¬ ValidPenaltyEvents excludedPrevious sampleCandidate
    ⟨1, [sampleEquivocation 0 7], []⟩ := by
  native_decide

/-- Reversed event order is a permutation, hence has the same successor. -/
example :
    [sampleEquivocation 0 7, sampleEquivocation 1 7].Perm
      [sampleEquivocation 1 7, sampleEquivocation 0 7] := by
  exact List.Perm.swap _ _ []

/-- A later candidate cannot restore an ejected key's active weight. -/
example :
    ((penaltySuccessor defaultSlashingConfig excludedPrevious sampleCandidate 1 ∅)
      ).account 0 = ⟨0, 75, true⟩ := by
  native_decide

end CordialMiners
