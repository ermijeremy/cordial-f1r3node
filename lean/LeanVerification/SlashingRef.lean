/-
Executable slashing reference and refinement proofs (#284).

Every decision below is over finite data. Arithmetic and successor semantics
are imported from the shared specification, rather than reimplemented here.
Crypto and finalization decisions must be supplied explicitly by the caller.
-/
import LeanVerification.CMRef
import LeanVerification.SlashingTransition

namespace CordialMiners.SlashingRef

variable {context : PenaltyAuthorizationContext}

/-- Stable fixture categories. Several map to Rust `InvalidPenaltyEvents`;
the finer categories retain the failed contract for conformance diagnostics. -/
inductive Error where
  | invalidConfiguration
  | invalidState
  | invalidEventRound
  | invalidValidatorSet
  | emptyEvidence
  | oversizedEvidence
  | tooManyEvents
  | duplicateOrOverlappingOffender
  | unknownOffender
  | alreadyEjectedOffender
  | unsupportedInactivity
  | inactiveRatingParticipant
  | arithmeticOverflow
  | structurallyInvalidEvidence
  | unauthenticatedEvidence
  | unauthorizedEvidence
  deriving DecidableEq, Repr

/-- Uses the existing finite KR2 checker, including observation and depth. -/
def checkEvidence (B : Blocklace) (hV : ValidBlocklace B)
    (evidence : RawEquivocationEvidence) : Bool :=
  CMRef.checkEquivocation B hV evidence.firstBlock evidence.secondBlock &&
    decide (creatorOf B evidence.firstBlock = some evidence.claimedOffender) &&
    decide (evidence.offenseRound = blockDepth B hV evidence.firstBlock)

theorem checkEvidence_iff (B : Blocklace) (hV : ValidBlocklace B)
    (evidence : RawEquivocationEvidence) :
    checkEvidence B hV evidence = true ↔ ValidEquivocationEvidence B hV evidence := by
  simp only [checkEvidence, Bool.and_eq_true, decide_eq_true_eq,
    CMRef.checkEquivocation_iff]
  constructor
  · rintro ⟨⟨hEq, hCreator⟩, hRound⟩
    rcases hEq with ⟨hFork, hDepth⟩
    rcases hFork with ⟨hFirst, hSecond, hSame, hDistinct, hNotFirst, hNotSecond⟩
    exact ⟨hFirst, hSecond, hDistinct, hSame, hCreator, hSame.symm.trans hCreator,
      hNotFirst, hNotSecond, hDepth, hRound,
      ⟨⟨hFirst, hSecond, hSame, hDistinct, hNotFirst, hNotSecond⟩, hDepth⟩⟩
  · intro h
    exact ⟨⟨h.equivocation, h.firstCreatorIsOffender⟩, h.offenseRoundIsFirstDepth⟩

/-- Proof-producing admission of raw evidence. The two `Decidable` values
are explicit trusted decisions for the *exact* evidence, decision and round.
They cannot be manufactured from a successful structural check or byte length. -/
def authorizeEvidence (B : Blocklace) (hV : ValidBlocklace B)
    (context : PenaltyAuthorizationContext) (evidence : RawEquivocationEvidence)
    (decision : PenaltyAuthorizationDecision) (applicationRound : Nat)
    (authentication : Decidable (EvidenceAuthenticated context.crypto B evidence))
    (authorization : Decidable
      (PenaltyApplicationAuthorized context.policy decision evidence applicationRound)) :
    Except Error (AuthorizedEquivocationEvent context) :=
  letI := authentication
  letI := authorization
  if hStructural : checkEvidence B hV evidence = true then
    if hAuthenticated : EvidenceAuthenticated context.crypto B evidence then
      if hAuthorized : PenaltyApplicationAuthorized context.policy decision evidence applicationRound then
        .ok (.ofAuthorizedPenaltyEvent B hV
          { evidence := evidence
            validEvidence := (checkEvidence_iff B hV evidence).mp hStructural
            authenticatedEvidence := hAuthenticated
            offender := evidence.claimedOffender
            offenderBound := rfl
            offenseRound := evidence.offenseRound
            offenseRoundBound := rfl
            applicationRound := applicationRound
            authorizationDecision := decision
            authorized := hAuthorized })
      else .error .unauthorizedEvidence
    else .error .unauthenticatedEvidence
  else .error .structurallyInvalidEvidence

theorem authorizeEvidence_success_iff (B : Blocklace) (hV : ValidBlocklace B)
    (context : PenaltyAuthorizationContext) (evidence : RawEquivocationEvidence)
    (decision : PenaltyAuthorizationDecision) (applicationRound : Nat)
    (authentication : Decidable (EvidenceAuthenticated context.crypto B evidence))
    (authorization : Decidable
      (PenaltyApplicationAuthorized context.policy decision evidence applicationRound)) :
    (∃ event, authorizeEvidence B hV context evidence decision applicationRound
      authentication authorization = .ok event) ↔
      ValidEquivocationEvidence B hV evidence ∧
      EvidenceAuthenticated context.crypto B evidence ∧
      PenaltyApplicationAuthorized context.policy decision evidence applicationRound := by
  let := authentication
  let := authorization
  by_cases hs : checkEvidence B hV evidence = true <;>
    by_cases ha : EvidenceAuthenticated context.crypto B evidence <;>
    by_cases hp : PenaltyApplicationAuthorized context.policy decision evidence applicationRound <;>
    simp [authorizeEvidence, hs, ha, hp, ← checkEvidence_iff B hV evidence]

/-! ## Checked arithmetic: reuse #282's executable definitions -/

abbrev validateConfig := validateSlashingConfig
abbrev selectTier := checkedSelectSlashPenalty
abbrev retained := checkedRetainedReputation

theorem validateConfig_iff (config : SlashingConfig) :
    validateConfig config = .ok () ↔ config.WellFormed ∧ config.FitsU64 := by
  unfold validateConfig validateSlashingConfig
  split
  · rename_i h
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rename_i h
    constructor
    · intro hOk
      cases hOk
    · intro hGood
      exact False.elim (h hGood)

/-- Bidirectional bounded arithmetic contract, including all accepted inputs. -/
theorem retained_iff (config : SlashingConfig) (old penalty result : Nat) :
    retained config old penalty = .ok result ↔
      config.WellFormed ∧ config.FitsU64 ∧
      old ≤ u64Max ∧ penalty ≤ u64Max ∧ penalty ≤ config.scale ∧
      old * (config.scale - penalty) ≤ u128Max ∧
      result = retainedReputation config old penalty := by
  unfold retained
  by_cases hc : config.WellFormed ∧ config.FitsU64
  · have hv : validateSlashingConfig config = .ok () := by
      simp [validateSlashingConfig, hc.1, hc.2]
    by_cases hw : u64Max < old ∨ u64Max < penalty
    · simp [checkedRetainedReputation, hv, hc.1, hc.2, hw,
        Bind.bind, Except.bind]
      omega
    · have ho : old ≤ u64Max := by omega
      have hp : penalty ≤ u64Max := by omega
      by_cases hs : penalty ≤ config.scale
      · by_cases hm : old * (config.scale - penalty) ≤ u128Max
        · rw [checkedRetainedReputation_refines config old penalty hc.1 hc.2 ho hp hs hm]
          simp [ho, hp, hs, hm, eq_comm]
          tauto
        · simp [checkedRetainedReputation, hv, hw,
            Nat.not_lt.mpr hs, checkedMulU128, hm, Bind.bind, Except.bind]
      · simp [checkedRetainedReputation, hv, hw,
          Nat.lt_of_not_ge hs, hs, Bind.bind, Except.bind]
  · have hv : validateSlashingConfig config = .error .invalidConfiguration := by
      simp only [validateSlashingConfig, hc, if_false]
    simp [checkedRetainedReputation, hv,
      Bind.bind, Except.bind]
    tauto

theorem selectTier_iff (config : SlashingConfig) (weight total result : Nat) :
    selectTier config weight total = .ok result ↔
      config.WellFormed ∧ config.FitsU64 ∧
      weight ≤ u128Max ∧ total ≤ u128Max ∧ 0 < total ∧ weight ≤ total ∧
      weight * config.scale ≤ u128Max ∧
      total * config.correlationThreshold ≤ u128Max ∧
      result = selectSlashPenalty config weight total := by
  unfold selectTier
  by_cases hc : config.WellFormed ∧ config.FitsU64
  · have hv : validateSlashingConfig config = .ok () := by
      simp [validateSlashingConfig, hc.1, hc.2]
    by_cases hw : u128Max < weight ∨ u128Max < total
    · simp [checkedSelectSlashPenalty, hv, hc.1, hc.2, hw,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      omega
    · have he : weight ≤ u128Max := by omega
      have ht : total ≤ u128Max := by omega
      by_cases hz : total = 0 ∨ total < weight
      · simp [checkedSelectSlashPenalty, hv, hc.1, hc.2, hw, hz,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
        omega
      · have hpos : 0 < total := by omega
        have hle : weight ≤ total := by omega
        by_cases hm : weight * config.scale ≤ u128Max
        · by_cases hn : total * config.correlationThreshold ≤ u128Max
          · rw [checkedSelectSlashPenalty_refines config weight total
              hc.1 hc.2 he ht hpos hle hm hn]
            simp [he, ht, hpos, hle, hm, hn, eq_comm]
            tauto
          · simp [checkedSelectSlashPenalty, hv, hw, hz,
              checkedMulU128, hm, hn, Bind.bind, Except.bind]
        · simp [checkedSelectSlashPenalty, hv, hw, hz,
            checkedMulU128, hm, Bind.bind, Except.bind]
  · have hv : validateSlashingConfig config = .error .invalidConfiguration := by
      simp only [validateSlashingConfig, hc, if_false]
    simp [checkedSelectSlashPenalty, hv,
      Bind.bind, Except.bind]
    tauto

/-! ## Finite admission and deterministic diagnostics -/

/-- Diagnostics do not decide acceptance. Acceptance uses the shared contract
below, so adding a diagnostic cannot weaken a specification precondition.
The precedence here is stable and independent of event order. -/
def diagnose (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents context) (ratingParticipants : List NodeId) : Error :=
  if ¬ (config.WellFormed ∧ config.FitsU64) ∨ config.scale < gamma then .invalidConfiguration
  else if ¬ (previous.WellFormed ∧ candidate.WellFormed) then .invalidState
  else if events.round ≠ previous.round + 1 ∨ candidate.round ≠ events.round then .invalidEventRound
  else if candidate.validatorIds ≠ previous.validatorIds then .invalidValidatorSet
  else if maxPenaltyEventCount < events.equivocations.length + events.inactivity.length then .tooManyEvents
  else if ∃ event ∈ events.equivocations, event.evidence = [] then .emptyEvidence
  else if ∃ event ∈ events.equivocations, maxPenaltyEvidenceLength < event.evidence.length then .oversizedEvidence
  else if ¬ (allPenaltyOffenders events).Nodup then .duplicateOrOverlappingOffender
  else if ∃ id ∈ allPenaltyOffenders events, id ∉ previous.validatorIds then .unknownOffender
  else if ∃ id ∈ allPenaltyOffenders events, (previous.account id).excluded = true then .alreadyEjectedOffender
  else if ∃ event ∈ events.equivocations, event.applicationRound ≠ events.round then .invalidEventRound
  else if ∃ event ∈ events.inactivity, event.missedRounds ≠ 1 then .unsupportedInactivity
  else if ∃ event ∈ events.inactivity, event.offender ∈ ratingParticipants then .inactiveRatingParticipant
  else if ∃ event ∈ events.inactivity, (candidate.account event.offender).excluded = true then .invalidState
  else if events.equivocations ≠ [] ∧ previousActiveTotal previous = 0 then .invalidConfiguration
  else .arithmeticOverflow

def validateTransition (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents context) (ratingParticipants : List NodeId) :
    Except Error Unit :=
  if ReferencePenaltyReady config gamma previous candidate events ratingParticipants then .ok ()
  else .error (diagnose config gamma previous candidate events ratingParticipants)

theorem validateTransition_iff (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents context) (ratingParticipants : List NodeId) :
    validateTransition config gamma previous candidate events ratingParticipants = .ok () ↔
      ReferencePenaltyReady config gamma previous candidate events ratingParticipants := by
  simp [validateTransition]

/-- All validation completes before exposing the pure staged successor.
Arithmetic readiness is precisely the precondition of the checked functions
proved above and in #282; no unchecked fixed-width operation is performed. -/
def transition (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents context) (ratingParticipants : List NodeId) :
    Except Error PenaltyReputationState := do
  validateTransition config gamma previous candidate events ratingParticipants
  pure (inactivityPenaltySuccessor config gamma previous candidate events)

/-- Soundness and completeness for the complete fieldwise successor relation. -/
theorem transition_iff (config : SlashingConfig) (gamma : Nat)
    (previous candidate successor : PenaltyReputationState)
    (events : PenaltyTransitionEvents context) (ratingParticipants : List NodeId) :
    transition config gamma previous candidate events ratingParticipants = .ok successor ↔
      ReferencePenaltyTransition config gamma previous candidate events ratingParticipants successor := by
  rw [referencePenaltyTransition_iff]
  by_cases h : ReferencePenaltyReady config gamma previous candidate events ratingParticipants <;>
    simp [transition, validateTransition, h, Bind.bind, Except.bind, Pure.pure, Except.pure]

def commit (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents context) (ratingParticipants : List NodeId) : PenaltyReputationState :=
  match transition config gamma previous candidate events ratingParticipants with
  | .ok successor => successor
  | .error _ => previous

theorem failure_atomic (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents context) (ratingParticipants : List NodeId) (error : Error)
    (h : transition config gamma previous candidate events ratingParticipants = .error error) :
    commit config gamma previous candidate events ratingParticipants = previous := by
  simp [commit, h]

theorem failure_no_successor (config : SlashingConfig) (gamma : Nat)
    (previous candidate successor : PenaltyReputationState)
    (events : PenaltyTransitionEvents context) (ratingParticipants : List NodeId) (error : Error)
    (h : transition config gamma previous candidate events ratingParticipants = .error error) :
    ¬ ReferencePenaltyTransition config gamma previous candidate events ratingParticipants successor := by
  rw [← transition_iff]
  simp [h]

/-- The complete model conservatively extends #283 on slash-only rounds. -/
theorem transition_noInactivity (config : SlashingConfig) (gamma : Nat)
    (previous candidate successor : PenaltyReputationState)
    (events : PenaltyTransitionEvents context) (ratingParticipants : List NodeId)
    (hReady : ReferencePenaltyReady config gamma previous candidate events ratingParticipants)
    (hEmpty : events.inactivity = []) :
    transition config gamma previous candidate events ratingParticipants = .ok successor ↔
      calculatePenaltyTransition config previous candidate events = .ok successor := by
  rcases hReady with ⟨hStates, hEvents, hEvidence, hBounds, hGamma, hRatings, hArithmetic⟩
  simp [transition, validateTransition,
    show ReferencePenaltyReady config gamma previous candidate events ratingParticipants from
      ⟨hStates, hEvents, hEvidence, hBounds, hGamma, hRatings, hArithmetic⟩,
    calculatePenaltyTransition, hStates, hEvents, hArithmetic,
    inactivityPenaltySuccessor_noInactivity config gamma previous candidate events hEmpty,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Supported inactivity uses exactly the bounded checked arithmetic of #282. -/
theorem inactivity_checked_refines (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents context) (ratingParticipants : List NodeId)
    (hReady : ReferencePenaltyReady config gamma previous candidate events ratingParticipants)
    (event : TransitionInactivityEvent) (hEvent : event ∈ events.inactivity) :
    checkedRetainedReputation config (previous.account event.offender).activeReputation gamma =
      .ok (retainedReputation config (previous.account event.offender).activeReputation gamma) := by
  rcases hReady with ⟨_, hEvents, _, hBounds, hGamma, _, hArithmetic⟩
  have hKnown := (List.forall_iff_forall_mem.mp hEvents.2.2.2.2.2 event hEvent).2.1
  have hOld := (hBounds.2.2.2.2 previous (by simp) event.offender hKnown).1
  have hGammaWidth := hGamma.trans hArithmetic.2.1.1
  have hProduct : (previous.account event.offender).activeReputation *
      (config.scale - gamma) ≤ u128Max := by
    calc
      _ ≤ u64Max * u64Max := Nat.mul_le_mul hOld
        ((Nat.sub_le _ _).trans hArithmetic.2.1.1)
      _ ≤ u128Max := by norm_num [u64Max, u128Max]
  exact checkedRetainedReputation_refines _ _ _ hArithmetic.1 hArithmetic.2.1
    hOld hGammaWidth hGamma hProduct

/-- Both event categories are unordered. This proves admission invariance,
including the finite width, size and inactive-rating checks. -/
theorem ready_permutation (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState)
    (first second : PenaltyTransitionEvents context) (ratingParticipants : List NodeId)
    (hRound : first.round = second.round)
    (hEq : first.equivocations.Perm second.equivocations)
    (hIn : first.inactivity.Perm second.inactivity) :
    ReferencePenaltyReady config gamma previous candidate first ratingParticipants ↔
      ReferencePenaltyReady config gamma previous candidate second ratingParticipants := by
  have hAll : (allPenaltyOffenders first).Perm (allPenaltyOffenders second) :=
    (hEq.map (fun (event : AuthorizedEquivocationEvent context) => event.offender)).append
      (hIn.map (fun (event : TransitionInactivityEvent) => event.offender))
  have hSets : first.equivocations.toFinset = second.equivocations.toFinset := List.toFinset_eq_of_perm _ _ hEq
  simp only [ReferencePenaltyReady, ValidPenaltyEvents, BoundedPenaltyEvidence,
    BoundedPenaltyInputs, List.forall_iff_forall_mem]
  rw [hRound, hAll.nodup_iff, hEq.length_eq, hIn.length_eq, hSets]
  simp only [hEq.mem_iff, hIn.mem_iff]

theorem successor_permutation (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState)
    (first second : PenaltyTransitionEvents context)
    (hRound : first.round = second.round)
    (hEq : first.equivocations.Perm second.equivocations)
    (hIn : first.inactivity.Perm second.inactivity) :
    inactivityPenaltySuccessor config gamma previous candidate first =
      inactivityPenaltySuccessor config gamma previous candidate second := by
  have hSets := List.toFinset_eq_of_perm _ _ hEq
  have hMembership : ∀ id : NodeId,
      id ∈ first.inactivity.map (·.offender) ↔ id ∈ second.inactivity.map (·.offender) :=
    fun _ => (hIn.map (fun event => event.offender)).mem_iff
  simp only [inactivityPenaltySuccessor, hRound, hSets, hMembership]

/-- Permutations reproduce every successful complete successor; by
completeness, a rejected input cannot become successful after reordering. -/
theorem transition_permutation (config : SlashingConfig) (gamma : Nat)
    (previous candidate successor : PenaltyReputationState)
    (first second : PenaltyTransitionEvents context) (ratingParticipants : List NodeId)
    (hRound : first.round = second.round)
    (hEq : first.equivocations.Perm second.equivocations)
    (hIn : first.inactivity.Perm second.inactivity) :
    transition config gamma previous candidate first ratingParticipants = .ok successor ↔
      transition config gamma previous candidate second ratingParticipants = .ok successor := by
  rw [transition_iff, transition_iff, referencePenaltyTransition_iff,
    referencePenaltyTransition_iff,
    ready_permutation config gamma previous candidate first second ratingParticipants hRound hEq hIn,
    successor_permutation config gamma previous candidate first second hRound hEq hIn]

theorem diagnose_permutation (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState)
    (first second : PenaltyTransitionEvents context) (ratingParticipants : List NodeId)
    (hRound : first.round = second.round)
    (hEq : first.equivocations.Perm second.equivocations)
    (hIn : first.inactivity.Perm second.inactivity) :
    diagnose config gamma previous candidate first ratingParticipants =
      diagnose config gamma previous candidate second ratingParticipants := by
  have hAll : (allPenaltyOffenders first).Perm (allPenaltyOffenders second) :=
    (hEq.map (fun (event : AuthorizedEquivocationEvent context) => event.offender)).append
      (hIn.map (fun (event : TransitionInactivityEvent) => event.offender))
  have hEmpty : first.equivocations = [] ↔ second.equivocations = [] := by
    constructor
    · intro h
      exact List.eq_nil_of_length_eq_zero (by rw [← hEq.length_eq, h]; rfl)
    · intro h
      exact List.eq_nil_of_length_eq_zero (by rw [hEq.length_eq, h]; rfl)
  have hNonempty : (first.equivocations ≠ []) ↔ (second.equivocations ≠ []) := not_congr hEmpty
  simp only [diagnose, hRound, hEq.length_eq, hIn.length_eq, hAll.nodup_iff,
    hEq.mem_iff, hIn.mem_iff, hAll.mem_iff, hNonempty]

/-- Complete result equality, including the category returned on failure. -/
theorem transition_permutation_eq (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState)
    (first second : PenaltyTransitionEvents context) (ratingParticipants : List NodeId)
    (hRound : first.round = second.round)
    (hEq : first.equivocations.Perm second.equivocations)
    (hIn : first.inactivity.Perm second.inactivity) :
    transition config gamma previous candidate first ratingParticipants =
      transition config gamma previous candidate second ratingParticipants := by
  simp only [transition, validateTransition,
    ready_permutation config gamma previous candidate first second ratingParticipants hRound hEq hIn,
    diagnose_permutation config gamma previous candidate first second ratingParticipants hRound hEq hIn,
    successor_permutation config gamma previous candidate first second hRound hEq hIn]

theorem successor_excluded_persistent (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState) (events : PenaltyTransitionEvents context)
    (id : NodeId) (hExcluded : (previous.account id).excluded = true) :
    (inactivityPenaltySuccessor config gamma previous candidate events).account id = previous.account id := by
  simp [inactivityPenaltySuccessor, hExcluded]

theorem successor_wellFormed (config : SlashingConfig) (gamma : Nat)
    (previous candidate : PenaltyReputationState)
    (events : PenaltyTransitionEvents context) (ratingParticipants : List NodeId)
    (hReady : ReferencePenaltyReady config gamma previous candidate events ratingParticipants) :
    (inactivityPenaltySuccessor config gamma previous candidate events).WellFormed := by
  rcases hReady with ⟨hStates, hEvents, _, _, _, hInactivity, _⟩
  have hSlashed := penaltySuccessor_wellFormed config previous candidate events.round
    events.equivocations.toFinset hStates.1 hStates.2 hEvents.2.2.1
  refine ⟨hSlashed.1, ?_⟩
  intro id hKnown
  change id ∈ previous.validatorIds at hKnown
  by_cases hExcluded : (previous.account id).excluded = true
  · simpa only [inactivityPenaltySuccessor, hExcluded, ↓reduceIte] using hStates.1.2 id hKnown
  · by_cases hInactive : id ∈ events.inactivity.map (·.offender)
    · obtain ⟨event, hEvent, hId⟩ := List.mem_map.mp hInactive
      have hCandidate : (candidate.account id).excluded = false := by
        simpa only [hId] using (hInactivity event hEvent).2
      have hDisjoint := (List.nodup_append.mp hEvents.2.2.2.1).2.2
      have hNoSlash : ¬ ∃ event ∈ events.equivocations.toFinset, event.offender = id := by
        rintro ⟨slash, hSlash, hSlashId⟩
        exact hDisjoint id (List.mem_map.mpr ⟨slash, List.mem_toFinset.mp hSlash, hSlashId⟩)
          id hInactive rfl
      have hOffender : isEquivocationOffender events.equivocations.toFinset id = false := by
        simp only [isEquivocationOffender, hNoSlash, decide_false]
      have hCandidateRetained := (hStates.2.2 id (by simpa [hEvents.2.2.1] using hKnown)).2 hCandidate
      simp only [inactivityPenaltySuccessor, hExcluded, hInactive, penaltySuccessor, hOffender,
        Bool.false_eq_true, ↓reduceIte, hCandidate, hCandidateRetained]
      simp
    · simpa only [inactivityPenaltySuccessor, hExcluded, hInactive, Bool.false_eq_true, ↓reduceIte] using
        hSlashed.2 id hKnown

theorem transition_ok_wellFormed (config : SlashingConfig) (gamma : Nat)
    (previous candidate successor : PenaltyReputationState)
    (events : PenaltyTransitionEvents context) (ratingParticipants : List NodeId)
    (h : transition config gamma previous candidate events ratingParticipants = .ok successor) :
    successor.WellFormed := by
  obtain ⟨hReady, rfl⟩ := (referencePenaltyTransition_iff _ _ _ _ _ _ _).mp
    ((transition_iff _ _ _ _ _ _ _).mp h)
  exact successor_wellFormed config gamma previous candidate events ratingParticipants hReady

/-- Finite exported-weight view for conformance fixtures. Unknown requested
identities and excluded keys both project to zero, per the formal definition. -/
def exportedWeights (state : PenaltyReputationState) (identities : List NodeId) : List (NodeId × Nat) :=
  identities.map fun id => (id, exportedActiveWeight state id)

theorem exportedWeights_equiv (state : PenaltyReputationState) (identities : List NodeId) :
    exportedWeights state identities = identities.map (fun id => (id, exportedActiveWeight state id)) := rfl

end CordialMiners.SlashingRef
