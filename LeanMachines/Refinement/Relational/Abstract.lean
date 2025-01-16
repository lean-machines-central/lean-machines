

import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Convergent

/-!

# Reusing abstract (deterministic, ordinary) events

This module establish generic principles for the
reuse of abstract events at the concrete level
 in case of a relational refinement.

This is a non-trivial issue in most cases, in that
there is no reason in general for an abstract event - working on the
abstract machine state - to be applicable on the
state of the concrete machine.

The reuse of abstract events should be easy (or a least easier) in
case of *superposition* refinement. This use case is covered by
the strong refinement principles (cf. `Refinement.Strong` modules).

In the proposed model, an abstract event specification must:

 - specify the abstract event to be reused

 - explain how the concrete state can be reflected at the abstract level
   (which is named, a `lift` operation)

 - explain how an abstract change is reflected at the concrete level
   (which is named, an `unlift` operation)

There are also two required proof obligations :

1. that the `lift` operation respects the `refine` (or glue) invariant
   connecting the concrete and abstract machines

2. a *functionality* argument for the refine (glue) invariant.

From this, we are able to prove that the abstract event can be
*safely* reused at the concrete level with two safety proof
obligations wrt. the `lift` and `unlift` operations.

**Important**: the `lift` function operates globally at the machine level.
Hence, a generally better approach is to adopt (at least) a functional refinement
approach,  cf. the `Refinement.Functional` modules.

However, the constructions below are required for the soundness
of the functional and strong refinement principles.

-/


open Refinement

/-!
## Transitional abstract events
-/

/-- Reuse of abstract events: the `lift ` part of machine-level requirements. -/
structure __AbstractREventSpec (AM) [@Machine ACTX AM]
                               (M) [@Machine CTX M]
                               [Refinement AM M] where
  /-- The construction of an abstract state from the concrete state `m`. -/
  lift (m: M) : AM

  /-- Proof obligation: the `lift` operation is safe wrt. the `refine` invariant.  -/
  lift_ref (m : M):
    Machine.invariant m → refine (lift m) m

  /-- Proof obligation: functionality constraint for the `refine` invariant. -/
  refine_uniq (am am' : AM) (m : M):
    Machine.invariant m
    → refine am m → refine am' m
    → am = am'


/-- Reuse of abstract events: the `unlift ` part of machine-level requirements. -/
structure _AbstractREventSpec (AM) [@Machine ACTX AM]
                              (M) [@Machine CTX M]
                              [Refinement AM M] (α)

  extends __AbstractREventSpec AM M  where

  /-- The reconstruction of a concrete state from an abstract state-change
  performed by the abstract event with input `x`. -/
  unlift (am am' : AM) (m : M) (x : α): M

/-- The specification of the reuse of an `abstract` event, with the
`lift` and `unlift` operations, the associated proof obligations,
 and the further two event-level proof obligations. -/
structure AbstractREventSpec (AM) [@Machine ACTX AM]
                             (M) [@Machine CTX M]
                            [Refinement AM M]
  {α β} (abstract : OrdinaryEvent AM α β)
          extends _AbstractREventSpec AM M α where

  /-- Proof obligation: lifting, then unlifting is safe wrt. the `refine` invariant. -/
  step_ref (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → let (_, am') := abstract.action (lift m) x agrd
      refine am' (unlift (lift m) am' m x)

  /-- Proof obligation: invariant preservation of the abstract event. -/
  step_safe (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → let (_, am') := abstract.action (lift m) x agrd
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m x)

/-- The construction of a reused abstract event (ordinary case).
Parameter `abs` is the event to reuse  (event of abstract machine)
Parameter `ev` is the reuse specification (cf. `AbstractREventSpec`). -/
@[simp]
def newAbstractREvent [@Machine ACTX AM] [@Machine CTX M] [instR:Refinement AM M]
  (abs : OrdinaryEvent AM α β) (ev : AbstractREventSpec AM M abs) : OrdinaryREvent AM M α β :=
  { guard := fun (m : M) (x : α) => abs.guard (ev.lift m) x
    action := fun (m : M) (x : α) grd =>
      let am := ev.lift m
      let (y, am') := abs.action am x grd
      (y, ev.unlift am am' m x)
    po := {
      safety := fun (m : M) (x : α) => by
        simp
        intros Hinv Hgrd
        have Href := ev.lift_ref m Hinv
        have Hainv := Refinement.refine_safe (ev.lift m) m Hinv Href
        have Hsafe := abs.po.safety (ev.lift m) x Hainv Hgrd
        apply ev.step_safe m x Hinv Hgrd Hsafe

      lift_in := id
      lift_out := id

      abstract := abs.to_Event

      strengthening := fun m x => by
        simp
        intros Hinv Hgrd am Href
        have Href' := ev.lift_ref m Hinv
        have Ham: am = ev.lift m := by
          apply ev.refine_uniq am (ev.lift m) m <;> assumption
        rw [Ham]
        assumption

      simulation := fun m x => by
        simp
        intros Hinv Hgrd am Href
        have Href' := ev.lift_ref m Hinv
        have Ham: am = ev.lift m := by
          apply ev.refine_uniq am (ev.lift m) m <;> assumption
        simp [Ham]
        apply ev.step_ref m x Hinv Hgrd
    }
  }

/-- Variant of `newAbstractREvent` with implicit `Unit` output type -/
@[simp]
def newAbstractREvent' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α Unit) (ev : AbstractREventSpec AM M abs) : OrdinaryREvent AM M α Unit :=
  newAbstractREvent abs ev

structure _AbstractREventSpec'' (AM) [@Machine ACTX AM]
                                (M) [@Machine CTX M]
                                [Refinement AM M]

  extends __AbstractREventSpec AM M  where

  unlift (am am' : AM) (m : M): M

/-- Variant of `AbstractREventSpec` with implicit `Unit` input and output types -/
structure AbstractREventSpec'' (AM) [@Machine ACTX AM]
                               (M) [@Machine CTX M]
                               [Refinement AM M]
  (abstract : OrdinaryEvent AM Unit Unit)
          extends _AbstractREventSpec'' AM M where

  step_ref (m : M):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) ())
    → let ((), am') := abstract.action (lift m) () agrd
      refine am' (unlift (lift m) am' m)

  step_safe (m : M):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) ())
    → let (_, am') := abstract.action (lift m) () agrd
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m)

@[simp]
def AbstractREventSpec''.toAbstractREventSpec [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
    (abs : OrdinaryEvent AM Unit Unit) (ev : AbstractREventSpec'' AM M abs) : AbstractREventSpec AM M abs :=
  {
    to__AbstractREventSpec := ev.to__AbstractREventSpec
    unlift := fun am am' m _ => ev.unlift am am' m
    step_ref := fun m () => ev.step_ref m
    step_safe := fun m () => ev.step_safe m
  }


/-- Variant of `newAbstractREvent` with implicit `Unit` input and output types -/
@[simp]
def newAbstractREvent'' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AbstractREventSpec'' AM M abs) : OrdinaryREvent AM M Unit Unit :=
  newAbstractREvent abs ev.toAbstractREventSpec

/-!
## Initialization abstract events
-/

/-- The specification of the reuse of an `abstract` initialization event,
with the `lift` and `unlift` operations, the associated proof obligations,
 and the further two event-level proof obligations. -/
structure AbstractInitREventSpec (AM) [@Machine ACTX AM]
                                 (M) [@Machine CTX M]
                                 [Refinement AM M]
  {α β} (abstract : InitEvent AM α β)
          extends _AbstractREventSpec AM M α where

  /-- Proof obligation: unlifting abstract state change is safe wrt. the `refine` invariant. -/
  step_ref (x : α):
    (agrd : abstract.guard x)
    → let (_, am') := abstract.init x agrd
      refine am' (unlift default am' default x)

  /-- Proof obligation: invariant preservation of the abstract event. -/
  step_safe (x : α):
    (agrd : abstract.guard x)
    → let (_, am') := abstract.init x agrd
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift default am' default x)

@[simp]
def AbstractInitREventSpec.to_InitEvent [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α β) (ev : AbstractInitREventSpec AM M abs) : _InitEvent M α β :=
  {
    guard := fun x => abs.guard x
    init := fun x grd => let (y, am') := abs.init x grd
                         (y, ev.unlift default am' default x)
  }

/-- The construction of a reused abstract initialization event.
Parameter `abs` is the event to reuse  (event of abstract machine)
Parameter `ev` is the reuse specification (cf. `AbstractInitREventSpec`). -/
@[simp]
def newAbstractInitREvent [@Machine ACTX AM] [@Machine CTX M] [instR:Refinement AM M]
  (abs : InitEvent AM α β) (ev : AbstractInitREventSpec AM M abs) : InitREvent AM M α β :=
  {
    to_InitEvent := ev.to_InitEvent
    po := {
      safety := fun x => by
        simp
        intro Hgrd
        have Hasafe := abs.po.safety x Hgrd
        have Hss := ev.step_safe x Hgrd Hasafe
        assumption

      lift_in := id
      lift_out := id

      abstract := abs.to_InitEvent

      strengthening := fun x => by simp
      simulation := fun x => by simp ; apply ev.step_ref
    }
  }

/-- Variant of `newAbstractInitREvent` with implicit `Unit` output type -/
@[simp]
def newAbstractInitREvent' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM α Unit) (ev : AbstractInitREventSpec AM M abs) : InitREvent AM M α Unit :=
  newAbstractInitREvent abs ev

/-- Variant of `AbstractInitREventSpec` with implicit `Unit` input and output types -/
structure AbstractInitREventSpec'' (AM) [@Machine ACTX AM]
                                 (M) [@Machine CTX M]
                                 [Refinement AM M]
  (abstract : InitEvent AM Unit Unit)
       extends _AbstractREventSpec'' AM M where

  step_ref:
    (agrd : abstract.guard ())
    → let ((), am') := abstract.init () agrd
      refine am' (unlift default am' default)

  step_safe :
    (agrd : abstract.guard ())
    → let ((), am') := abstract.init () agrd
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift default am' default)

@[simp]
def AbstractInitREventSpec''.toAbstractInitREventSpec [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
    (abs : InitEvent AM Unit Unit) (ev : AbstractInitREventSpec'' AM M abs) : AbstractInitREventSpec AM M abs :=
  {
    to__AbstractREventSpec := ev.to__AbstractREventSpec
    unlift := fun am am' m _ => ev.unlift am am' m
    step_ref := fun () => ev.step_ref
    step_safe := fun () => ev.step_safe
  }

/-- Variant of `newAbstractInitREvent` with implicit `Unit` input and output types -/
@[simp]
def newAbstractRInitEvent'' [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : InitEvent AM Unit Unit) (ev : AbstractInitREventSpec'' AM M abs) : InitREvent AM M Unit Unit :=
  newAbstractInitREvent abs ev.toAbstractInitREventSpec

/-!
## Anticipated abstract events
-/

/-- Reuse of abstract anticipated event.
The requirements are thow of `AbstractREventSpec` with a demonstration
that the abstract variant is preserved when reflected at the concrete level. -/
structure AbstractAnticipatedREventSpec
              (v) [Preorder v]
              (AM) [@Machine ACTX AM]
              (M) [@Machine CTX M]
              [Refinement AM M]
  {α β} (abstract : AnticipatedEvent v AM α β)
          extends AbstractREventSpec AM M abstract.toOrdinaryEvent where

  /-- Proof obligation: the abstract variant is preserved at the concrete level. -/
  step_variant (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → let (_, am') := abstract.action (lift m) x agrd
      Machine.invariant am' -- redundant but useful
      → abstract.po.variant (lift (unlift (lift m) am' m x))
      = abstract.po.variant am'

/-- The construction of a reused abstract event (anticipated case).
Parameter `abs` is the event to reuse  (event of abstract machine)
Parameter `ev` is the reuse specification (cf. `AbstractREventSpec`). -/
@[simp]
def newAbstractAnticipatedREvent [Preorder v]
                                 [@Machine ACTX AM]
                                 [@Machine CTX M]
                                 [instR:Refinement AM M]
  (abs : AnticipatedEvent v AM α β) (ev : AbstractAnticipatedREventSpec v AM M abs) : AnticipatedREvent v AM M α β :=
  let oev := newAbstractREvent abs.toOrdinaryEvent ev.toAbstractREventSpec
  {
    to_Event := oev.to_Event
    po := {
      safety := oev.po.safety
      lift_in := oev.po.lift_in
      lift_out := oev.po.lift_out
      abstract := abs.to_Event
      strengthening := oev.po.strengthening
      simulation := oev.po.simulation

      variant := fun m => abs.po.variant (ev.lift m)

      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd
        have Hinv' := Refinement.refine_safe (ev.lift m) m Hinv (ev.lift_ref m Hinv)
        have Hainv := abs.po.safety (ev.lift m) x Hinv' Hgrd
        have Hni := abs.po.nonIncreasing (ev.lift m) x Hinv' Hgrd
        simp at Hni
        have Hsv := ev.step_variant m x Hinv Hgrd Hainv
        simp [oev]
        rw [Hsv]
        assumption
    }
  }

/-- Variant of `newAbstractAnticipatedREvent` with implicit `Unit` output type -/
@[simp]
def newAbstractAnticipatedREvent' [Preorder v]
                                  [@Machine ACTX AM]
                                  [@Machine CTX M]
                                  [Refinement AM M]
  (abs : AnticipatedEvent v AM α Unit) (ev : AbstractAnticipatedREventSpec v AM M abs) : AnticipatedREvent v AM M α Unit :=
  newAbstractAnticipatedREvent abs ev

/-- Variant of `AbstractAnticipatedREventSpec` with implicit `Unit` input and output types -/
structure AbstractAnticipatedREventSpec''
              (v) [Preorder v]
              (AM) [@Machine ACTX AM]
              (M) [@Machine CTX M]
              [Refinement AM M]
  (abstract : AnticipatedEvent v AM Unit Unit)
          extends AbstractREventSpec'' AM M abstract.toOrdinaryEvent where

  step_variant (m : M):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) ())
    → let ((), am') := abstract.action (lift m) () agrd
      Machine.invariant am' -- redundant but useful
      → abstract.po.variant (lift (unlift (lift m) am' m))
      = abstract.po.variant am'

@[simp]
def AbstractAnticipatedREventSpec''.toAbstractAnticipatedREventSpec [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit) (ev : AbstractAnticipatedREventSpec'' v AM M abs) : AbstractAnticipatedREventSpec v AM M abs :=
  {
    to__AbstractREventSpec := ev.to__AbstractREventSpec
    unlift := fun am am' m _ => ev.unlift am am' m
    step_ref := fun m _ => ev.step_ref m
    step_safe := fun m _ => ev.step_safe m
    step_variant := fun m _ => ev.step_variant m
  }

/-- Variant of `newAbstractAnticipatedREvent` with implicit `Unit` output type -/
@[simp]
def newAbstractAnticipatedREvent'' [Preorder v]
                                  [@Machine ACTX AM]
                                  [@Machine CTX M]
                                  [Refinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit) (ev : AbstractAnticipatedREventSpec'' v AM M abs) : AnticipatedREvent v AM M Unit Unit :=
  newAbstractAnticipatedREvent abs ev.toAbstractAnticipatedREventSpec

/-- The construction of a reused abstract event (convergent case).
Parameter `abs` is the event to reuse  (event of abstract machine)
Parameter `ev` is the reuse specification (cf. `AbstractREventSpec`). -/
@[simp]
def newAbstractConvergentREvent  [Preorder v] [WellFoundedLT v]
                                 [@Machine ACTX AM]
                                 [@Machine CTX M]
                                 [instR:Refinement AM M]
  (abs : ConvergentEvent v AM α β) (ev : AbstractAnticipatedREventSpec v AM M abs.toAnticipatedEvent) : ConvergentREvent v AM M α β :=
  let oev := newAbstractAnticipatedREvent abs.toAnticipatedEvent ev
  {
    to_Event := oev.to_Event
    po := {
      safety := oev.po.safety
      lift_in := oev.po.lift_in
      lift_out := oev.po.lift_out
      abstract := abs.to_Event
      strengthening := oev.po.strengthening
      simulation := oev.po.simulation
      variant := oev.po.variant
      nonIncreasing := oev.po.nonIncreasing

      convergence := fun m x => by
        simp [oev]
        intros Hinv Hgrd
        have Hinv' := Refinement.refine_safe (ev.lift m) m Hinv (ev.lift_ref m Hinv)
        have Hainv := abs.po.safety (ev.lift m) x Hinv' Hgrd
        have Hcv := abs.po.convergence (ev.lift m) x Hinv' Hgrd
        simp at Hcv
        have Hsv := ev.step_variant m x Hinv Hgrd Hainv
        simp at Hsv
        rw [Hsv]
        assumption
    }
  }

/-- Variant of `newAbstractConvergentREvent` with implicit `Unit` output type -/
@[simp]
def newAbstractConvergentREvent'  [Preorder v] [WellFoundedLT v]
                                  [@Machine ACTX AM]
                                  [@Machine CTX M]
                                  [Refinement AM M]
  (abs : ConvergentEvent v AM α Unit) (ev : AbstractAnticipatedREventSpec v AM M abs.toAnticipatedEvent) : ConvergentREvent v AM M α Unit :=
  newAbstractConvergentREvent abs ev

/-- Variant of `newAbstractConvergentREvent` with implicit `Unit` input and output types -/
@[simp]
def newAbstractConvergentREvent''  [Preorder v] [WellFoundedLT v]
                                   [@Machine ACTX AM]
                                   [@Machine CTX M]
                                   [Refinement AM M]
  (abs : ConvergentEvent v AM Unit Unit) (ev : AbstractAnticipatedREventSpec'' v AM M abs.toAnticipatedEvent) : ConvergentREvent v AM M Unit Unit :=
  newAbstractConvergentREvent abs ev.toAbstractAnticipatedREventSpec
