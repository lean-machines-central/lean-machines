
import LeanMachines.NonDet.Ordinary
import LeanMachines.Refinement.Relational.NonDet.Basic
import LeanMachines.Refinement.Relational.NonDet.Convergent
import LeanMachines.Refinement.Relational.Abstract

/-!

# Reusing abstract non-deterministic events

This module establish generic principles for the
reuse of abstract non-deterministic events at the concrete level
 in case of a relational refinement.

**Important**: like for the deterministic case, it is simpler to
reuse abstract events in the case of functional refinement,
 or event better, strong refinement, when applicable.

cf. module `Refinement.Relational.Abstract` (deterministic case) for
more informations about the reuse model.

-/

open Refinement

/-!
## Transitional abstract events
-/

/-- Reuse of abstract events: the `lift/unlift` part specific to non-determinism.
(machine-level properties are the same as in the deterministic case). -/
structure _AbstractRNDEventSpec (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [Refinement AM M] (α)
          extends _AbstractREventSpec AM M α where

  /-- Proof obligation: lifting an unlifted abstract state change is invariant
  (a kind of functionality constraint). -/
  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

/-- The specification of the reuse of an `abstract` non-deterministic
event, with the `lift` and `unlift` operations, the associated proof obligations,
 and the further two event-level proof obligations specific to non-determinism. -/
structure AbstractRNDEventSpec (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [Refinement AM M]
  {α β} (abstract : OrdinaryNDEvent AM α β)
          extends _AbstractRNDEventSpec AM M α where

  /-- Proof obligation: lifting, then unlifting is safe wrt. the `refine` invariant. -/
  step_ref (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → ∀ y, ∀ am', abstract.effect (lift m) x agrd (y, am')
                  → refine am' (unlift (lift m) am' m x)

  /-- Proof obligation: invariant preservation of the abstract event. -/
  step_safe (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → ∀ y, ∀ am', abstract.effect (lift m) x agrd (y, am')
                  → Machine.invariant (unlift (lift m) am' m x)

/-- The construction of a reused non-deterministic abstract event (ordinary case).
Parameter `abs` is the event to reuse  (event of abstract machine)
Parameter `ev` is the reuse specification (cf. `AbstractRNDEventSpec`). -/
@[simp]
def newAbstractRNDEvent [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : OrdinaryNDEvent AM α β) (ev : AbstractRNDEventSpec AM M abs) : OrdinaryRNDEvent AM M α β :=
  {
    guard := fun m x => abs.guard (ev.lift m) x
    effect := fun m x grd (y, m') => abs.effect (ev.lift m) x grd (y, ev.lift m')
                                     ∧ m' = ev.unlift (ev.lift m) (ev.lift m') m x
    po := {
      lift_in := id
      lift_out := id
      safety := fun m x => by
        simp
        intros Hinv Hagrd y m' Heff Hm'
        rw [Hm']
        apply ev.step_safe m x Hinv Hagrd y (ev.lift m') Heff

      feasibility := fun m x => by
        simp
        intros Hinv Hagrd
        have Href := ev.lift_ref m Hinv
        have Hainv := refine_safe (ev.lift m) m Hinv Href
        obtain ⟨y, am', Hafeas⟩ := abs.po.feasibility (ev.lift m) x Hainv Hagrd
        exists y
        exists (ev.unlift (ev.lift m) am' m x)
        have Hsref := ev.step_ref m x Hinv Hagrd y am' Hafeas
        have Hssafe := ev.step_safe m x Hinv Hagrd y am' Hafeas
        have Hasafe' := refine_safe am' (ev.unlift (ev.lift m) am' m x) Hssafe Hsref
        have Hlu := ev.lift_unlift m (ev.lift m) am' x Hinv Hasafe'
        rw [Hlu]
        simp [Hafeas]

      abstract := abs.to_NDEvent

      strengthening := fun m x => by
        simp
        intros Hinv Hagrd am Href
        have Href' := ev.lift_ref m Hinv
        have Huniq := ev.refine_uniq am (ev.lift m) m Hinv Href Href'
        rw [Huniq]
        exact Hagrd

      simulation := fun m x => by
        simp
        intros Hinv Hagrd y m' Heff Hm' am Href
        have Href' := ev.lift_ref m Hinv
        exists (ev.lift m')
        constructor
        · have Huniq := ev.refine_uniq am (ev.lift m) m Hinv Href Href'
          simp [Huniq]
          exact Heff
        -- and
        rw [Hm']
        rw [ev.lift_unlift]
        · apply ev.step_ref m x Hinv Hagrd y (ev.lift m') Heff
        · assumption
        -- finally
        have Hainv := refine_safe (ev.lift m) m Hinv Href'
        apply abs.po.safety (ev.lift m) x Hainv Hagrd y (ev.lift m') Heff
    }
  }

/-- Variant of `AbstractRNDEventSpec` with implicit `Unit` input type -/
structure AbstractRNDEventSpec' (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [Refinement AM M]
  {α} (abstract : OrdinaryNDEvent AM α Unit)
          extends _AbstractRNDEventSpec AM M α where

  step_ref (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → ∀ am', abstract.effect (lift m) x agrd ((), am')
             → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → ∀ am', abstract.effect (lift m) x agrd ((), am')
             → Machine.invariant (unlift (lift m) am' m x)

@[simp]
def AbstractRNDEventSpec'.toAbstractRNDEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (abs : OrdinaryNDEvent AM α Unit) (ev : AbstractRNDEventSpec' AM M abs) : AbstractRNDEventSpec AM M abs :=
  {
    to_AbstractRNDEventSpec := ev.to_AbstractRNDEventSpec
    step_ref := fun m x => by
      intros Hinv Hgrd _ am' Heff
      apply ev.step_ref <;> assumption
    step_safe := fun m x => by
      intros Hinv Hgrd _ am' Heff
      apply ev.step_safe <;> assumption
  }


/-- Variant of `newAbstractRNDEvent` with implicit `Unit` input type -/
@[simp]
def newAbstractRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α Unit) (ev : AbstractRNDEventSpec' AM M abs) : OrdinaryRNDEvent AM M α Unit :=
  newAbstractRNDEvent abs ev.toAbstractRNDEventSpec

structure _AbstractRNDEventSpec'' (AM) [Machine ACTX AM]
                                  (M) [Machine CTX M]
                                  [Refinement AM M]
          extends _AbstractREventSpec'' AM M where

  lift_unlift (m : M) (am am' : AM):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m) = am'


/-- Variant of `AbstractRNDEventSpec` with implicit `Unit` input and output types -/
structure AbstractRNDEventSpec'' (AM) [Machine ACTX AM]
                                 (M) [Machine CTX M]
                                 [Refinement AM M]
  (abstract : OrdinaryNDEvent AM Unit Unit)
          extends _AbstractRNDEventSpec'' AM M where

  step_ref (m : M):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) ())
    → ∀ am', abstract.effect (lift m) () agrd ((), am')
             → refine am' (unlift (lift m) am' m)

  step_safe (m : M):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) ())
    → ∀ am', abstract.effect (lift m) () agrd ((), am')
             → Machine.invariant (unlift (lift m) am' m)

@[simp]
def AbstractRNDEventSpec''.toAbstractRNDEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (abs : OrdinaryNDEvent AM Unit Unit) (ev : AbstractRNDEventSpec'' AM M abs) : AbstractRNDEventSpec AM M abs :=
  {
    to__AbstractREventSpec := ev.to__AbstractREventSpec
    unlift := fun am am' m _ => ev.unlift am am' m
    lift_unlift := fun m am am' _ => ev.lift_unlift m am am'
    step_ref := fun m () => by
      intros Hinv Hgrd _ am' Heff
      apply ev.step_ref <;> assumption
    step_safe := fun m () => by
      intros Hinv Hgrd _ am' Heff
      apply ev.step_safe <;> assumption
  }

/-- Variant of `newAbstractRNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newAbstractRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : AbstractRNDEventSpec'' AM M abs) : OrdinaryRNDEvent AM M Unit Unit :=
  newAbstractRNDEvent abs ev.toAbstractRNDEventSpec

/-!
## Initialization abstract events
-/


/-- The specification of the reuse of an `abstract` non-deterministic
initialization event, with the `lift` and `unlift` operations,
the associated proof obligations,  and further three event-level proof obligations. -/
structure AbstractInitRNDEventSpec (AM) [Machine ACTX AM]
                                   (M) [Machine CTX M]
                                  [Refinement AM M]
  {α β} (abstract : InitNDEvent AM α β)
          extends _AbstractREventSpec AM M α where

  /-- Proof obligation:  lifting abstract state change is invariant
  (a kind of functionality). -/
  lift_unlift (am' : AM) (x : α):
    Machine.invariant am'
    → lift (unlift Machine.reset am' Machine.reset x) = am'

  /-- Proof obligation: unlifting abstract state change is safe wrt. the `refine` invariant. -/
  step_ref (x : α):
    (agrd : abstract.guard x)
    → ∀ y, ∀ am', abstract.init x agrd (y, am')
                  → refine am' (unlift Machine.reset am' Machine.reset x)

  /-- Proof obligation: invariant preservation of the abstract event. -/
  step_safe (x : α):
    (agrd : abstract.guard x)
    → ∀ y, ∀ am', abstract.init x agrd (y, am')
                  → Machine.invariant (unlift Machine.reset am' Machine.reset x)

@[simp]
def AbstractInitRNDEventSpec.to_InitNDEvent  [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM α β) (ev : AbstractInitRNDEventSpec AM M abs) : _InitNDEvent M α β  :=
  {
    guard := abs.guard
    init := fun x grd (y, m') => ∃ am', abs.init x grd (y, am')
                                 ∧ m' =  ev.unlift Machine.reset am' Machine.reset x
  }

/-- The construction of a reused non-deterministic abstract initialization event.
Parameter `abs` is the event to reuse  (event of abstract machine)
Parameter `ev` is the reuse specification (cf. `AbstractInitRNDEventSpec`). -/
@[simp]
def newAbstractInitRNDEvent [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : InitNDEvent AM α β) (ev : AbstractInitRNDEventSpec AM M abs) : InitRNDEvent AM M α β :=
  {
    to_InitNDEvent := ev.to_InitNDEvent
    po := {
      lift_in := id
      lift_out := id
      safety := fun x => by
        simp
        intros Hagrd y m' am' Hini Hm'
        -- no use for abstract safety (except in proving step_safe in practice)
        -- have Hsafe := abs.po.safety x Hagrd y (ev.lift m')
        have Hss := ev.step_safe x Hagrd y (ev.lift m')
        rw [Hm'] at Hss
        rw [Hm']
        have Hainv := abs.po.safety x Hagrd y am' Hini
        have Hlu := ev.lift_unlift am' x Hainv
        rw [←Hlu] at Hini
        have Hss' := Hss Hini ; clear Hss
        rw [Hlu] at Hss'
        assumption

      feasibility := fun x => by
        simp
        intros Hagrd
        obtain ⟨y, am', Hafeas⟩ := abs.po.feasibility x Hagrd
        exists y
        exists (ev.unlift Machine.reset am' Machine.reset x)
        exists am'

      abstract := abs.to_InitNDEvent

      strengthening := fun x => by simp

      simulation := fun x => by
        simp
        intros Hagrd y m' am' Hini Hm'
        have Hainv := abs.po.safety x Hagrd y am' Hini
        exists (ev.lift m')
        constructor
        · rw [Hm']
          have Hlu := ev.lift_unlift am' x Hainv
          rw [Hlu]
          assumption
        -- and
        rw [Hm']
        rw [ev.lift_unlift]
        · apply ev.step_ref x Hagrd y am' Hini
        -- finally
        assumption
    }
  }

/-- Variant of `AbstractInitRNDEventSpec` with implicit `Unit` output type -/
structure AbstractInitRNDEventSpec' (AM) [Machine ACTX AM]
                                   (M) [Machine CTX M]
                                  [Refinement AM M]
  {α} (abstract : InitNDEvent AM α Unit)
          extends _AbstractREventSpec AM M α where

  lift_unlift (am' : AM) (x : α):
    Machine.invariant am'
    → lift (unlift Machine.reset am' Machine.reset x) = am'

  step_ref (x : α):
    (agrd : abstract.guard x)
    → ∀ am', abstract.init x agrd ((), am')
             → refine am' (unlift Machine.reset am' Machine.reset x)

  step_safe (x : α):
    (agrd : abstract.guard x)
    → ∀ am', abstract.init x agrd ((), am')
             → Machine.invariant (unlift Machine.reset am' Machine.reset x)

/-- Variant of `AbstractInitRNDEventSpec` with implicit `Unit` output type -/
@[simp]
def AbstractInitRNDEventSpec'.toAbstractInitRNDEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abstract : InitNDEvent AM α Unit)
  (ev : AbstractInitRNDEventSpec' AM M abstract) : AbstractInitRNDEventSpec AM M abstract :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    lift_unlift := ev.lift_unlift
    step_ref := fun x => by
      intros Hagrd _ am' Heff
      apply ev.step_ref <;> assumption
    step_safe := fun x => by
      intros Hagrd _ am' Heff
      apply ev.step_safe <;> assumption
  }

/-- Variant of `newAbstractInitRNDEvent` with implicit `Unit` output type -/
@[simp]
def newAbstractInitRNDEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM α Unit) (ev : AbstractInitRNDEventSpec' AM M abs) : InitRNDEvent AM M α Unit :=
  newAbstractInitRNDEvent abs ev.toAbstractInitRNDEventSpec

/-- Variant of `AbstractInitRNDEventSpec` with implicit `Unit` input and output types -/
structure AbstractInitRNDEventSpec'' (AM) [Machine ACTX AM]
                                     (M) [Machine CTX M]
                                     [Refinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
          extends _AbstractREventSpec'' AM M where

  lift_unlift (am' : AM):
    Machine.invariant am'
    → lift (unlift Machine.reset am' Machine.reset) = am'

  step_ref:
    (agrd : abstract.guard ())
    → ∀ am', abstract.init () agrd ((), am')
             → refine am' (unlift Machine.reset am' Machine.reset)

  step_safe:
    (agrd : abstract.guard ())
    → ∀ am', abstract.init () agrd ((), am')
             → Machine.invariant (unlift Machine.reset am' Machine.reset)

@[simp]
def AbstractInitRNDEventSpec''.toAbstractInitRNDEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
  (ev : AbstractInitRNDEventSpec'' AM M abstract) : AbstractInitRNDEventSpec AM M abstract :=
  {
    to__AbstractREventSpec := ev.to__AbstractREventSpec
    unlift := fun am am' m _ => ev.unlift am am' m
    lift_unlift := fun am () => ev.lift_unlift am
    step_ref := fun x => by
      intros Hagrd _ am' Heff
      apply ev.step_ref <;> assumption
    step_safe := fun x => by
      intros Hagrd _ am' Heff
      apply ev.step_safe <;> assumption
  }

/-- Variant of `newAbstractInitRNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newAbstractInitRNDEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : InitNDEvent AM Unit Unit) (ev : AbstractInitRNDEventSpec'' AM M abs) : InitRNDEvent AM M Unit Unit :=
  newAbstractInitRNDEvent abs ev.toAbstractInitRNDEventSpec

/-!
## Anticipated abstract events
-/

/-- Reuse of an abstract anticipated event with `abs` a non-deterministic anticipated event.
The requirements are those of `AbstractRNDEventSpec`. -/
@[simp]
def newAbstractAnticipatedRNDEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : AnticipatedNDEvent v AM α β) (ev : AbstractRNDEventSpec AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α β :=
  let aev := newAbstractRNDEvent abs.toOrdinaryNDEvent ev
  {
    to_NDEvent := aev.to_NDEvent
    po := {
      safety :=aev.po.safety
      feasibility := aev.po.feasibility
      lift_in := aev.po.lift_in
      lift_out := aev.po.lift_out
      abstract := abs.to_NDEvent
      strengthening := aev.po.strengthening
      simulation := aev.po.simulation

      variant := fun m => abs.po.variant (ev.lift m)
      nonIncreasing := fun m x => by
        simp [aev]
        intros Hinv Hgrd y m' Heff _
        have Hinv' := Refinement.refine_safe (ev.lift m) m Hinv (ev.lift_ref m Hinv)
        apply abs.po.nonIncreasing (ev.lift m) x Hinv' Hgrd y (ev.lift m') Heff
    }
  }

/-- Variant of `newAbstractAnticipatedRNDEvent` with implicit `Unit` output type -/
@[simp]
def newAbstractAnticipatedRNDEvent' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM α Unit) (ev : AbstractRNDEventSpec' AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α Unit :=
  newAbstractAnticipatedRNDEvent abs ev.toAbstractRNDEventSpec

/-- Variant of `AbstractAnticipatedRNDEventSpec` with implicit `Unit` input and output types -/
@[simp]
def newAbstractAnticipatedRNDEvent'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM Unit Unit) (ev : AbstractRNDEventSpec'' AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAbstractAnticipatedRNDEvent abs ev.toAbstractRNDEventSpec

/-- Reuse of an abstract convergent event with `abs` a non-deterministic convergent event.
The requirements are those of `AbstractRNDEventSpec`. -/
@[simp]
def newAbstractConvergentRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR:Refinement AM M]
  (abs : ConvergentNDEvent v AM α β) (ev : AbstractRNDEventSpec AM M abs.toAnticipatedNDEvent.toOrdinaryNDEvent) : ConvergentRNDEvent v AM M α β :=
  let aev := newAbstractAnticipatedRNDEvent abs.toAnticipatedNDEvent ev
  {
    to_NDEvent := aev.to_NDEvent
    po := {
      safety :=aev.po.safety
      feasibility := aev.po.feasibility
      lift_in := aev.po.lift_in
      lift_out := aev.po.lift_out
      abstract := abs.to_NDEvent
      strengthening := aev.po.strengthening
      simulation := aev.po.simulation
      variant := aev.po.variant
      nonIncreasing := aev.po.nonIncreasing
      convergence := fun m x => by
        simp [aev]
        intros Hinv Hgrd y m' Heff _
        have Hinv' := Refinement.refine_safe (ev.lift m) m Hinv (ev.lift_ref m Hinv)
        apply abs.po.convergence (ev.lift m) x Hinv' Hgrd y (ev.lift m') Heff
    }
  }

/-- Variant of `newAbstractConvergentRNDEvent` with implicit `Unit` output type. -/
@[simp]
def newAbstractConvergentRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : ConvergentNDEvent v AM α Unit) (ev : AbstractRNDEventSpec' AM M abs.toAnticipatedNDEvent.toOrdinaryNDEvent) : ConvergentRNDEvent v AM M α Unit :=
  newAbstractConvergentRNDEvent abs ev.toAbstractRNDEventSpec

/-- Variant of `newAbstractConvergentRNDEvent` with implicit `Unit` input and output types. -/
@[simp]
def newAbstractConvergentRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : ConvergentNDEvent v AM Unit Unit) (ev : AbstractRNDEventSpec'' AM M abs.toAnticipatedNDEvent.toOrdinaryNDEvent) : ConvergentRNDEvent v AM M Unit Unit :=
  newAbstractConvergentRNDEvent abs ev.toAbstractRNDEventSpec
