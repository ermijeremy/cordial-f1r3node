/- Executable conformance-boundary regressions for #284. -/
import LeanVerification.SlashingRef
import LeanVerification.SlashingTransitionExamples

namespace CordialMiners.SlashingRefExamples

open SlashingRef SlashingTransitionExamples

private def previous : PenaltyReputationState :=
  ⟨0, [0, 1, 2, 3], fun _ => ⟨100, 0, false⟩⟩

/-- Candidate rewards must not affect slash tiers or inactivity deductions. -/
private def candidate : PenaltyReputationState :=
  ⟨1, [0, 1, 2, 3], fun _ => ⟨200, 0, false⟩⟩

private def events (offenders : List NodeId) (inactive : List NodeId := []) :
    PenaltyTransitionEvents sampleContext :=
  ⟨1, offenders.map sampleEquivocation, inactive.map (fun id => ⟨id, 1⟩)⟩

private def errorOf (result : Except Error α) : Option Error :=
  match result with
  | .ok _ => none
  | .error error => some error

private def run (input : PenaltyTransitionEvents sampleContext)
    (ratings : List NodeId := []) : Except Error PenaltyReputationState :=
  transition defaultSlashingConfig 10_000_000 previous candidate input ratings

private def balances (result : Except Error PenaltyReputationState) :
    Option (Nat × List ValidatorReputation) :=
  match result with
  | .ok state => some (state.round, state.validatorIds.map state.account)
  | .error _ => none

example : checkEvidence (forkView 0) (forkView_valid 0) (sampleEvidence 0) = true := by
  native_decide

example : checkEvidence (forkView 0) (forkView_valid 0)
    { sampleEvidence 0 with claimedOffender := 1 } = false := by native_decide

example : checkEvidence (forkView 0) (forkView_valid 0)
    { sampleEvidence 0 with secondBlock := (sampleEvidence 0).firstBlock } = false := by native_decide

example : checkEvidence (forkView 0) (forkView_valid 0)
    { sampleEvidence 0 with offenseRound := 1 } = false := by native_decide

example : checkEvidence emptyBlocklace ValidBlocklace.empty (sampleEvidence 0) = false := by
  native_decide

example : errorOf (authorizeEvidence (forkView 0) (forkView_valid 0) sampleContext
    (sampleEvidence 0) (.attested 0) 1 (.isTrue True.intro) (.isTrue ⟨rfl, rfl⟩)) = none := by
  native_decide

private def deniedCrypto : PenaltyAuthorizationContext :=
  { sampleContext with crypto := ⟨fun _ _ => False⟩ }

example : errorOf (authorizeEvidence (forkView 0) (forkView_valid 0) deniedCrypto
    (sampleEvidence 0) (.attested 0) 1 (.isFalse id) (.isTrue ⟨rfl, rfl⟩)) =
      some .unauthenticatedEvidence := by native_decide

example : errorOf (authorizeEvidence (forkView 0) (forkView_valid 0) sampleContext
    (sampleEvidence 0) (.attested 0) 2 (.isTrue True.intro)
    (.isFalse (by simp [PenaltyApplicationAuthorized, sampleContext]))) =
      some .unauthorizedEvidence := by native_decide

example : balances (run (events [0])) =
    some (1, [⟨0, 75, true⟩, ⟨200, 0, false⟩, ⟨200, 0, false⟩, ⟨200, 0, false⟩]) := by
  native_decide

example : balances (run (events [0, 1])) =
    some (1, [⟨0, 0, true⟩, ⟨0, 0, true⟩, ⟨200, 0, false⟩, ⟨200, 0, false⟩]) := by
  native_decide

example : balances (run (events [1, 0])) = balances (run (events [0, 1])) := by native_decide

/-- Inactivity uses 100 from the previous state, giving 99, rather than 198. -/
example : balances (run (events [0] [1])) =
    some (1, [⟨0, 75, true⟩, ⟨99, 0, false⟩, ⟨200, 0, false⟩, ⟨200, 0, false⟩]) := by
  native_decide

example : errorOf (run (events [0, 0])) = some .duplicateOrOverlappingOffender := by native_decide
example : errorOf (run (events [0] [0])) = some .duplicateOrOverlappingOffender := by native_decide
example : errorOf (run (events [] [0, 0])) = some .duplicateOrOverlappingOffender := by native_decide
example : errorOf (run (events [9])) = some .unknownOffender := by native_decide
example : errorOf (run (events [] [0]) [0]) = some .inactiveRatingParticipant := by native_decide
example : errorOf (run { events [] with round := 2 }) = some .invalidEventRound := by native_decide
example : errorOf (run ⟨1, [], [⟨0, 2⟩]⟩) = some .unsupportedInactivity := by native_decide

example : errorOf (transition defaultSlashingConfig 10_000_000 previous
    { candidate with account := fun _ => ⟨0, 0, true⟩ } (events [] [0]) []) =
      some .invalidState := by native_decide

private def withBytes (bytes : List UInt8) : AuthorizedEquivocationEvent sampleContext :=
  .ofAuthorizedPenaltyEvent (forkView 0) (forkView_valid 0)
    { sampleAuthorizedPenalty 0 with
      evidence := { sampleEvidence 0 with proofMaterial := bytes }
      validEvidence := by
        apply (checkEvidence_iff _ _ _).mp
        simpa only [checkEvidence] using
          (checkEvidence_iff _ _ _).mpr (sampleEvidence_valid 0) }

example : errorOf (run ⟨1, [withBytes []], []⟩) = some .emptyEvidence := by native_decide
example : errorOf (run ⟨1, [withBytes (List.replicate (64 * 1024 + 1) 0)], []⟩) =
    some .oversizedEvidence := by native_decide
example : errorOf (run ⟨1, [withBytes (List.replicate (64 * 1024) 0)], []⟩) = none := by native_decide
example : errorOf (run ⟨1, [], List.replicate 1_000_001 ⟨0, 1⟩⟩) =
    some .tooManyEvents := by native_decide

example : selectTier defaultSlashingConfig 30 100 = .ok 250_000_000 := by native_decide
example : selectTier defaultSlashingConfig 3_000_000_001 10_000_000_000 = .ok 1_000_000_000 := by
  native_decide
example : retained defaultSlashingConfig 10 250_000_000 = .ok 7 := by native_decide

private def wideConfig : SlashingConfig := ⟨u64Max, 0, 0, u64Max⟩
private def widePrevious : PenaltyReputationState :=
  ⟨0, [0, 1], fun _ => ⟨u64Max, 0, false⟩⟩

example : errorOf (transition wideConfig 0 widePrevious { widePrevious with round := 1 }
    (events [0, 1]) []) = some .arithmeticOverflow := by native_decide

/-- Full-state atomicity is proved generally; observe round and accounts here. -/
example :
    let state := commit wideConfig 0 widePrevious { widePrevious with round := 1 }
      (events [0, 1]) []
    (state.round, state.validatorIds.map state.account) =
      (0, [⟨u64Max, 0, false⟩, ⟨u64Max, 0, false⟩]) := by native_decide

private def ejected : PenaltyReputationState :=
  { previous with account := fun id => if id = 0 then ⟨0, 75, true⟩ else previous.account id }

example : errorOf (transition defaultSlashingConfig 0 ejected candidate (events [0]) []) =
    some .alreadyEjectedOffender := by native_decide

example : (commit defaultSlashingConfig 0 ejected candidate (events []) []).account 0 =
    ⟨0, 75, true⟩ := by native_decide

example : exportedWeights (commit defaultSlashingConfig 0 ejected candidate (events []) [])
    [0, 1, 9] = [(0, 0), (1, 200), (9, 0)] := by native_decide

private def zero : PenaltyReputationState := ⟨0, [0], fun _ => ⟨0, 0, false⟩⟩

example : errorOf (transition defaultSlashingConfig 0 zero { zero with round := 1 }
    (events []) []) = none := by native_decide
example : errorOf (transition defaultSlashingConfig 0 zero { zero with round := 1 }
    (events [] [0]) []) = none := by native_decide
example : errorOf (transition defaultSlashingConfig 0 zero { zero with round := 1 }
    (events [0]) []) = some .invalidConfiguration := by native_decide

example : errorOf (transition { defaultSlashingConfig with scale := 0 } 0
    previous candidate (events []) []) = some .invalidConfiguration := by native_decide
example : errorOf (transition defaultSlashingConfig (defaultSlashingConfig.scale + 1)
    previous candidate (events []) []) = some .invalidConfiguration := by native_decide
example : errorOf (transition defaultSlashingConfig 0 previous
    { candidate with validatorIds := [1, 0] } (events []) []) = some .invalidState := by native_decide
example : errorOf (transition defaultSlashingConfig 0 previous
    { candidate with account := fun _ => ⟨u64Max + 1, 0, false⟩ } (events []) []) =
      some .arithmeticOverflow := by native_decide

end CordialMiners.SlashingRefExamples
